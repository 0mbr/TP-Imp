(**
   La traduction de EIMP vers MIPS est immédiate pour la plupart des
   instructions "de base". Il reste à traiter deux choses principales :
   - traduire les instructions de contrôle if et while à l'aide de sauts,
   - réaliser les convention d'appel pour les fonction, côté appelé.

   Convention d'appel, pour la fonction appelée :
   - Au début de l'appel, il faut stocker sur la pile
     * la valeur courante du pointeur $fp (qui contient le pointeur
       de base du tableau d'activation de la fonction appelante), et
     * la valeur courante de $ra.
     Il faut ensuite redéfinir le registre $fp pour qu'il représente cette
     fois le pointeur de base du tableau d'activation de la fonction appelée,
     et décaler $sp de sorte à réserver l'espace nécessaire aux variables
     locales.
   - À la fin de l'appel, il faut s'assurer que le résultat est stocké dans
     le registre $v0, remettre à jour $sp pour libérer l'espace de pile
     utilisé par le tableau d'activation de la fonction, puis restaurer
     les valeurs de $ra et $fp qui avaient été sauvegardées avant de rendre
     la main.
 *)

open Eimp
open Mips

let push r = sw r 0 sp @@ subi sp sp 4

let temp_real_regs = [Mips.t2; Mips.t3; Mips.t4; Mips.t5; Mips.t6; Mips.t7; Mips.t8; Mips.t9; Mips.s0];;

(* Fonction de création de nouvelles étiquettes, à utiliser notamment pour
   traduire les boucles et les branchements. *)
let new_label =
  let count = ref 0 in
  fun () -> incr count; Printf.sprintf "__lab_%i" !count

(**
   Fonction de traduction d'une fonction.
 *)
let tr_fdef fdef =

  (* Proposition : utiliser un point de retour unique pour tous les return
     (ou même en absence de return !). Cette étiquette est prévue pour cela. *)
  let return_label = new_label() in

  (* Traduction des isntructions : relativement direct, sauf pour les 
     branchements et les boucles *)
  let rec tr_instr = function
    | Putchar r          -> move a0 r @@ li v0 11 @@ syscall
    | Read(rd, Global x) -> la rd x @@  lw rd 0 rd
    | Read(rd, Stack i)  -> lw rd (4*i) sp
    | Read(rd, Param i)  -> lw rd (4*i) fp
    | Write(Global x, r) -> la a1 x @@ sw r 0 a1
    | Write(Stack i, r)  -> sw r (4*i) sp
    | Write(Param i, r)  -> sw r (4*i) fp
    | Move(rd, r)        -> move rd r
    | Push r             -> sw r 0 sp @@ subi sp sp 4
    | Pop n              -> addi sp sp (4*n)
    | Cst(rd, n)         -> li rd n
    | Unop(rd, Addi n, r)    -> addi rd r n
    | Binop(rd, Add, r1, r2) -> add rd r1 r2
    | Binop(rd, Mul, r1, r2) -> mul rd r1 r2
    | Binop(rd, Lt, r1, r2)  -> slt rd r1 r2
    | Call(f)            -> jal f
    | If(r, s1, s2) -> let true_label = new_label() in 
                       let end_label = new_label() in
                       bnei r 0 true_label 
                       @@ tr_seq s1 @@ b end_label 
                       @@ label true_label @@ tr_seq s2
                       @@ label end_label
    | While(s1, r, s2) -> let loop_label = new_label() in 
                          let end_label = new_label() in
                          label loop_label 
                          @@ tr_seq s1
                          @@ beqz r end_label
                          @@ tr_seq s2 @@ b loop_label
                          @@ label end_label
    | Return -> b return_label

  and tr_seq (s: Eimp.sequence) = match s with
    | Nop         -> nop
    | Instr i     -> tr_instr i
    | Seq(s1, s2) -> tr_seq s1 @@ tr_seq s2
  in

  (* Code de la fonction. Il faut prévoir notamment ici, dans l'ordre
     - la convention d'appel, phase "début de l'appel",
     - le code de la fonction elle-même,
     - le point de retour unique,
     - la convention d'appel, phase "fin d'appel",
     - rendre la main.
   *)
  push fp
  @@ push ra
  @@ addi fp sp 8
  @@ sw "$t2" 0 sp @@ sw "$t3" (-4) sp @@ sw "$t4" (-8) sp @@ sw "$t5" (-12) sp 
  @@ sw "$t6" (-16) sp @@ sw "$t7" (-20) sp @@ sw "$t8" (-24) sp @@ sw "$t9" (-28) sp
  @@ addi sp sp (-32)
  @@ addi sp sp (-4 * fdef.locals)

  @@ tr_seq fdef.code

  @@ label return_label
  (*@@ li t0 0*)
  @@ move sp fp
  @@ lw "$t2" (-8) sp @@ lw "$t3" (-12) sp @@ lw "$t4" (-16) sp @@ lw "$t5" (-20) sp 
  @@ lw "$t6" (-24) sp @@ lw "$t7" (-28) sp @@ lw "$t8" (-32) sp @@ lw "$t9" (-36) sp
  @@ lw ra (-4) fp
  @@ lw fp 0 fp
  @@ jr ra


(**
   Fonction principale, de traduction d'un programme entier.
   Au-delà de la traduction de chaque fonction, on a
   - une initialisation qui donne la main à "main",
   - une fonction prédéfinie pour décoder un entier passsé en ligne de commande,
   - la déclaration des données globales.

   Attention, dans le code prédéfini d'initialisation il y a une adaptation à
   faire selon la convention d'appel (voir commentaire suivant).          
 *)
let tr_prog prog =
  let init =
    beqz a0 "init_end"
    @@ lw a0 0 a1
    @@ jal "atoi"
    @@ label "init_end"
    (* Choix selon votre convention d'appel 
         move a0 v0 
       dans le cas où les premiers paramètres passent par les registres,
       mais 
         sw v0 0 sp
         subi sp sp 4
       dans le cas où tous passent par la pile.
     *)
    @@ sw v0 0 sp
    @@ subi sp sp 4
    (* Choix : ici, on a sélectionné la version passant par la pile. *)
    @@ jal "main"
    (* Après l'exécution de la fonction "main", appel système de fin de
       l'exécution. *)
    @@ li v0 10
    @@ syscall
  and built_ins =
    (* Fonction de conversion chaîne -> entier, à base d'une boucle sur les
       caractères de la chaîne. *)
    comment "built-in atoi"
    @@ label "atoi"
    @@ li   v0 0
    @@ label "atoi_loop"
    @@ lbu  t0 0 a0
    @@ beqz t0 "atoi_end"
    @@ addi t0 t0 (-48)
    @@ bltz t0 "atoi_error"
    @@ bgei t0 10 "atoi_error"
    @@ muli v0 v0 10
    @@ add  v0 v0 t0
    @@ addi a0 a0 1
    @@ b "atoi_loop"
    @@ label "atoi_error"
    @@ li   v0 10
    @@ syscall
    @@ label "atoi_end"
    @@ jr   ra
  in

  (**
     Code principal pour générer le code MIPS associé au programme source.
   *)
  let function_codes = List.fold_right
    (fun fdef code ->
      label fdef.name @@ tr_fdef fdef @@ code)
    prog.functions nop
  in
  let text = init @@ function_codes @@ built_ins
  and data = List.fold_right
    (fun id code -> label id @@ dword [0] @@ code)
    prog.globals nop
  in
  
  { text; data }
  
