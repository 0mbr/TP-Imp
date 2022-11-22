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

(* Type pour l'assertion d'utilisation d'un registre dans une fonction *)
module SMap = Map.Make(String)
module VSet = Set.Make(String)

open Eimp
open Mips

let push r = sw r 0 sp @@ subi sp sp 4
let pop  r = lw r 0 sp @@ addi sp sp 4

(* Fonction de création de nouvelles étiquettes, à utiliser notamment pour
   traduire les boucles et les branchements. *)
let new_label =
  let count = ref 0 in
  fun () -> incr count; Printf.sprintf "__lab_%i" !count

let push_regs reglist offset =
  let n = List.length reglist in
  let seq, _ = List.fold_left 
    (fun (seq, i) r -> (seq @@ sw r (-(i+offset)*4) sp), (i+1)) 
    (Nop, 0) reglist
  in 
  seq @@ subi sp sp (4*(n+offset))

let pop_regs reglist offset =
  let n = List.length reglist in
  let seq, _ = List.fold_right 
    (fun r (seq, i) -> (seq @@ lw r ((i+offset)*4) sp), (i+1)) 
    reglist (Nop, 0) 
  in 
  seq @@ addi sp sp (4*(n+offset))

let seq_jump_save_callees = 
  sw ra (-4*(List.length callee_saved)) sp 
  @@ jal lab_callees_save    
  @@ lw ra 0 sp

let seq_jump_save_callers = 
  sw ra (-4*(List.length caller_saved)) sp 
  @@ jal lab_callers_save    
  @@ lw ra 0 sp

let seq_jump_restore_callees = 
  sw ra (-4) sp
  @@ jal lab_callees_restore    
  @@ lw ra (-(4*(List.length callee_saved) + 4)) sp

let seq_jump_restore_callers = 
  sw ra (-4) sp
  @@ jal lab_callers_restore    
  @@ lw ra (-(4*(List.length caller_saved) + 4)) sp 

let seq_save_callees    = label lab_callees_save    @@ push_regs callee_saved 0 @@ jr ra
let seq_restore_callees = label lab_callees_restore @@ pop_regs  callee_saved 0 @@ jr ra
let seq_save_callers    = label lab_callers_save    @@ push_regs caller_saved 0 @@ jr ra
let seq_restore_callers = label lab_callers_restore @@ pop_regs  caller_saved 0 @@ jr ra

(*let seq_save_callees2    = push_regs callee_saved 0
let seq_restore_callees2 = pop_regs  callee_saved 0
let seq_save_callers2    = push_regs caller_saved 0
let seq_restore_callers2 = pop_regs  caller_saved 0*)

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
    | Call(f) -> 
      if f = lab_callers_save then
        seq_jump_save_callers
      else if f = lab_callers_restore then
        seq_jump_restore_callers
      else 
        let n = fdef.params in
        let clean_args_seq = if n <= pmax then Nop 
                            else addi sp sp (4*n) in
        jal f @@ clean_args_seq
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
  @@ seq_jump_save_callees
  @@ subi sp sp (4 * fdef.locals)

  @@ tr_seq fdef.code

  @@ label return_label
  @@ subi sp fp (8 + 4*(List.length callee_saved)) (* on retourne au niveau des callee saved pour les restaurer *)
  @@ seq_jump_restore_callees
  @@ addi sp fp 4 (* sp pointe sur le dernier caller-saved ou argument enregistré *)
  @@ lw ra (-8) sp
  @@ lw fp (-4) sp
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
    @@ move a0 v0
    (* Choix : ici, on a sélectionné la version passant par registres. *)
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
  and routines =
    comment "callees and callers -saved routines" 
    @@ seq_save_callees
    @@ seq_restore_callees
    @@ seq_save_callers
    @@ seq_restore_callers
  in

  (**
     Code principal pour générer le code MIPS associé au programme source.
   *)
  let function_codes = List.fold_right
    (fun fdef code ->
      label fdef.name @@ tr_fdef fdef @@ code)
    prog.functions nop
  in
  let text = init @@ function_codes @@ routines @@ built_ins
  and data = List.fold_right
    (fun id code -> label id @@ dword [0] @@ code)
    prog.globals nop
  in
  
  { text; data }
  
