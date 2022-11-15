(**
   Traduction simple de IMP vers MIPS.

   Résumé de l'architecture et des instructions MIPS.


   Architecture 32 bits avec :
   - une unité de calcul
   - 32 registres
     * usage général : $t0-$t9, $s0-$s7, $a0-$a3, $v0-$v1
     * spéciaux : $ra, $sp, $fp, $gp, $zero
     (+3 réservés)
   - une mémoire adressable, contenant code et données


   Un programme MIPS contient deux parties :
   - des instructions, introduites par l'annotation

       .text

   - des données, introduites par l'annotation

       .data

   La partie des données contient les données qui peuvent être allouées
   statiquement, typiquement les variables globales du programme.
   Chaque donnée est désignée par une étiquette qui permettra d'y faire
   référence.



   *** Arithmétique ***

   Instructions arithmétiques au format "trois adresses", appliquées
   à des valeurs contenues dans des registres, et plaçant le résultat
   dans un registre.
   Format trois adresses :

     add  $r1, $r2, $r3

   signifie  $r1 <- $r2 + $r3 
   où $r1 est le registre où sera enregistrée le résultat, et $r2 et 
   $r3 les registres contenant les valeurs à  additionner.
   
   On a sur ce format : 
   - de l'arithmétique : add, sub, mul, div, rem, sll, srl
   - des opérateurs logiques : and, or
   - des opérateurs de comparaison : seq, sne, slt, sle, sgt, sge
   Aussi quelques opérations unaires où on ne fournit qu'un seul opérande :
   - not, neg, move


   Certains instructions arithmétiques prennent pour deuxième opérande
   un nombre entier. Par exemple :

     addi  $r1, $r2, i

   pour  $r1 <- $r2 + i


   Charger une valeur dans un registre

     li  $r, i

   pour  $r <- i


   *** Mémoire ***

   Une adresse mémoire est identifiée par un décalage [d] (une valeur
   entière) à partir d'une adresse de base contenue dans un registre [$r].
   Notation : d($r). L'unité de mesure est l'octet. Une donnée 32 bits
   compte donc 4 octets.

   Accès en lecture

     lw  $r1, d($r2)

   pour  $r1 <- *($r2+d)
   c'est-à-dire "$r1 reçoit la valeur stockée à l'adresse $r2+d".

   Accès en écriture

     sw  $r1, d($r2)

   pour  *($r2+d) <- $r1
   c'est-à-dire "écrire à l'adresse $r2+d la valeur du registre $r1".


   Les données statiques sont, comme le reste, stockées en mémoire.
   On récupère l'adresse associée à l'étiquette [lab] d'une donnée statique
   avec
   
     la  $r1, lab


   *** Instructions de branchement ***

   Le programme en cours d'exécution est stocké dans la mémoire, chaque
   instruction a donc une adresse. Le registre spécial [pc] contient 
   l'adresse de la prochaine instruction à exécuter.

   En temps normal, après exécution d'une instruction donnée on poursuit
   avec l'instruction située immédiatement après en mémoire, ce qui
   correspond à
     pc <- pc + 4
   Les instructions de saut permettent de désigner un autre point de code
   avec lequel poursuivre,
   - soit à l'aide d'une étiquette écrite dans le code assembleur,
   - soit en fournissant directement (via un registre) une nouvelle valeur
     pour [pc].

   Sauts inconditionnels vers une étiquette (on ignorera la différence entre
   les deux).
     
     j  lab
     b  lab

   Saut inconditionnel vers une adresse donnée par un registre

     jr  $r

   Variantes utilisées pour les appels de fonction, qui stockent la valeur
   [pc+4] dans le registre spécial $ra. Cette adresse enregistrée désigne
   l'instruction à laquelle il faudra reprendre l'exécution lorsque l'appel
   de fonction sera terminé.

     jal   lab
     jalr  $r


   Sauts conditionnels vers une étiquette en fonction du résultat d'un test.
   Exemple : saute à l'instruction d'étiquette [lab] si les valeurs contenues
   dans les registres $r1 et $r2 sont égales.

     beq  $r1, $r2, lab

   Tests disponibles
   - beq, bne, bgt, bge, blt, ble

   Cas particuliers avec un seul registre, qui revient à fixer $r2=0

     beqz  $r1, lab

   Avec de même les test
   - beqz, bnez, bgtz, bgez, bltz, blez


   *** Appels système ***

   Instruction spéciale
     
     syscall

   pour déclencher un effet particulier.
   Code de l'effet souhaité à placer dans le registre $v0.
   Argument éventuel à placer dans le registre $a0.

   Quelques exemples :
   - code 1 : affiche l'entier contenu dans le registre $a0
   - code 10 : fin de l'exécution du programme
   - code 11 : affiche le caractère dont le code ASCII est donné par $a0

 *)

(**
   Le module Imp contient la syntaxe abstraite source.
   Le module Mips contient des fonctions caml générant des instructions MIPS.
 *)
open Imp
open Mips

   
(**
   La partie supérieure de la mémoire (les adresses les plus hautes) est 
   utilisée comme une pile pour stocker différents éléments utiles.
   Le registre spécial $sp désigne le sommet de la pile (plus précisément,
   la première adresse libre au sommet de la pile). La pile grandit dans le
   sens des adresses décroissantes.
   On définit deux fonctions auxiliaires [push] et [pop] pour générer du
   code MIPS ajoutant ou retirant un élément de la pile.
 *)
(* Pour sauvegarder la valeur d'un registre [reg], on écrit cette valeur à 
   l'adresse désignée par $sp puis on décrémente $sp de 4 octets. 
   Note : l'opérateur @@ concatène des fragments de code MIPS (il est fourni 
   par le module Mips). *)
let push reg =
  sw reg 0 sp
  @@ subi sp sp 4
(* Inversement, pour récupérer le dernier élément de la pile et le placer
   dans un registre [reg], on incrémente $sp de 4 puis on lit la valeur 
   contenue dans la mémoire à l'adresse $sp mise à jour. *)
let pop  reg =
  addi sp sp 4
  @@ lw reg 0 sp
(* Dans les deux cas précédents, la mise à jour de $sp assure que la
   prochaine utilisation de la pile tiendra bien compte du fait que la pile
   a été agrandie ou réduite. *)

(**
   Fonction générant le code MIPS associé à une fonction IMP.
   Les fonctions générant du code MIPS pour des expressions ou des 
   instructions seront définies à l'intérieur.
 *)
let tr_function fdef =
  (**
     Mise en place d'une table pour l'accès aux variables locales et
     aux paramètres fournis à la fonction lors de son appel.
     Ces données seront disposée en mémoire de part et d'autre d'une
     adresse désignée par le pointeur spécial $fp. L'ensemble dessiné
     ci-dessous est appelé table d'activation de l'appel.
     
       +------+
       |  aN  |   <- dernier argument, adresse  $fp + 4N
       +------+
       |      |
       |  ..  |
       |      |
       +------+
       |  a2  |   <- deuxième argument, adresse $fp + 8
       +------+
       |  a1  |   <- premier argument, adresse $fp + 4
       +------+
       |      |   <- adresse de référence $fp
       +------+
       |      |
       +------+
       |  x1  |   <- première variable locale, adresse $fp - 8
       +------+
       |  x2  |   <- deuxième variable locale, adresse $fp - 12
       +------+
       |      |
       |  ..  |
       |      |
       +------+
       |  xK  |   <- dernière variable locale, adresse $fp - 4(K+1)
       +------+

     La table définie ci-dessous associe à chaque variable locale ou
     paramètre le décalage à appliquer à partir de l'adresse de référence.
   *)
  let env = Hashtbl.create 16 in
  List.iteri (fun k id -> Hashtbl.add env id (4*(k+1))) fdef.params;
  List.iteri (fun k id -> Hashtbl.add env id (-4*(k+2))) fdef.locals;
  (**
     Dans le tableau d'activation, les cases d'adresse $fp et $fp-4 sont
     utilisées pour deux informations particulières, non accessibles par
     le programme source.
     - À l'adresse $fp, on stocke l'adresse de référence du tableau 
       d'activation de l'appelant. On obtient ainsi un chaînage des tableaux
       d'activation de tous les appels de fonction en cours, avec en tête
       le plus récent.
     - À l'adresse $fp-4, on stocke l'adresse de retour de l'appel, 
       c'est-à-dire l'adresse à laquelle il faudra poursuivre une fois
       l'appel terminé. C'est l'adresse qui est placée dans $ra au moment
       de l'appel. On la sauvegarde dans le tableau d'activation pour
       éviter qu'elle ne se fasse écraser par l'appel suivant.
   *)
  

  
  (** 
     Fonction générant le code MIPS associé à une expression.
     La fonction prend en paramètre une expression [e] et produit une
     séquence d'instructions MIPS qui évalue [e] et place la valeur
     obtenue dans le registre $t0. 
   *)
  let rec tr_expr = function
    (* Cas d'une valeur constante : on charge directement la valeur dans
       le registre cible $t0. On code la valeur booléenne [true] par 1
       et la valeur booléenne [false] par 0. *)
    | Cst(n)  -> li t0 n
    | Bool(b) -> if b then li t0 1 else li t0 0

    (* Cas d'une variable. On cherche l'identifiant dans la table locale [env]
       pour connaître le décalage associé à cette variable. Il suffit alors
       d'utiliser une instruction de lecture appliquant ce décalage à partir
       de l'adresse de référence $fp. *)
    | Var(id) -> begin
        match Hashtbl.find_opt env id with
        | Some offset -> lw t0 offset fp
        (* Si l'identifiant n'apparaît pas dans [env], c'est qu'il s'agit 
           d'une variable globale. On utilise alors cet identifiant comme une 
           étiquette et on récupère l'adresse associée. *)
        | None -> la t0 id @@ lw t0 0 t0
      end
               
    (* Opération binaire : on utilise la pile pour stocker les valeurs
       intermédiaires jusqu'à leur utilisation. *)
    | Binop(bop, e1, e2) ->
       let op = match bop with
         | Add -> add
         | Mul -> mul
         | Lt  -> slt
       in
       (* Évaluer [e2] *)
       tr_expr e2
       (* Sauvegarder sur la pile la valeur de [e2], que le code précédent
          a placée dans le registre $t0. *)
       @@ push t0
       (* Évaluer [e1] *)
       @@ tr_expr e1
       (* Récupérer la valeur de [e2] qui avait été sauvegardée sur la pile,
          et la mettre dans un registre autre que $t0 (puisque ce dernier
          contient la valeur de [e1]). *)
       @@ pop t1
       (* Appliquer l'opération binaire à $t0 (valeur de [e1]) et $t1 (valeur
          de [e2]), et placer le résultat dans $t0. *)
       @@ op t0 t0 t1      

    (* Appel de fonction.
       Avant de passer la main à la fonction elle-même on évalue tous les
       arguments et on place leurs valeurs sur la pile, du dernier au premier.
     *)
    | Call(f, params) ->
       (* Évaluation des arguments et passage sur la pile. *)
       let params_code =
         List.fold_right
           (fun e code -> code @@ tr_expr e @@ push t0)
           params nop
       in
       params_code
       (* Ici, le sommet de la pile a la forme 

            +------+
            |  aN  |
            +------+
            |      |
            |  ..  |
            |      |
            +------+
            |  a2  |
            +------+
            |  a1  |
            +------+
            |      |  <-  adresse désignée par $sp

          Rappel : le "sommet" de la pile est son adresse la plus basse.
          Ce sommet de la pile forme la première partie du tableau 
          d'activation. La deuxième partie, concernant les variables locales,
          sera construite par la fonction elle-même. *) 
       (* Appel de fonction, en sauvegardant l'adresse de retour dans $ra. *)
       @@ jal f
       (* Une fois l'appel terminé, on revient à ce point du code, et le
          registre $t0 contient la valeur renvoyée. *)
       (* On conclut la procédure d'appel en retirant de la pile les arguments
          qui y avaient été placés. Il suffit pour cela de modifier $sp. *)
       @@ addi sp sp (4 * List.length params)

  in

  (**
     Fonction auxiliaire pour générer des étiquettes uniques, qui
     seront utilisées dans la traduction des structures de contrôle
     (instructions if et while).
   *)
  let new_label =
    let cpt = ref (-1) in
    fun () -> incr cpt; Printf.sprintf "__%s_%i" fdef.name !cpt
  in

  (**
     Fonctions générant le code MIPS associé à une instruction ou à une
     séquence d'instructions.
   *)
  let rec tr_seq = function
    | []   -> nop
    | [i]  -> tr_instr i
    (* Si la séquence contient plusieurs instructions, les séquences
       d'instructions correspondantes sont placées à la suite les unes
       des autres, dans l'ordre. *)
    | i::s -> tr_instr i @@ tr_seq s

  and tr_instr = function
    (* Affichage d'un caractère. *)
    | Putchar(e) ->
       (* Évaluer l'expression [e] *)
       tr_expr e
       (* On déplace la valeur de [e] de $t0 (où elle a été produite)
          vers $a0 (où elle doit être pour l'appel à syscall). *)
       @@ move a0 t0
       (* Appel système numéro 11 : affichage d'un caractère. *)
       @@ li v0 11
       @@ syscall
        
    (* Affectation.
       Après évaluation de [e], sa valeur est dans $t0.
       Selon que la variable est locale ou globale, on utilise des
       instructions MIPS différentes pour mettre à jour la mémoire
       avec cette valeur $t0. *)
    | Set(id, e) ->
       let set_code = match Hashtbl.find_opt env id with
         | Some offset -> sw t0 offset fp
         | None -> la t1 id @@ sw t0 0 t1
       in
       tr_expr e @@ set_code

    (* Branchement *)
    | If(c, s1, s2) ->
       (* On crée deux étiquettes en prévision des sauts. *)
       let then_label = new_label()
       and end_label = new_label()
       in
       (* Évaluation de la condition [c] *)
       tr_expr c
       (* Si la valeur de la condition est non nulle, et donc interprétée
          comme [true], on saute au morceau de code correspondant à la
          branche "then"... *)
       @@ bnez t0 then_label
       (* ... sinon on passe à l'instruction suivante.
          On place donc le code de la branche "else" ici. *)
       @@ tr_seq s2
       (* À la fin du code de la branche "else", on place un saut vers
          l'instruction suivant le branchement. *)
       @@ b end_label
       (* Bloc de code de la branche "then". *)
       @@ label then_label
       @@ tr_seq s1
       (* À la fin du bloc de code de la branche "then" pas besoin de
          saut, car nous sommes justement à la fin du code du branchement
          complet. On place simplement ici l'étiquette de fin, sans rien
          derrière. *)
       @@ label end_label

    (* Boucle *)
    | While(c, s) ->
       (* On crée deux étiquettes en prévision des sauts. *)
       let test_label = new_label()
       and code_label = new_label()
       in
       (* Première instruction : sauter vers le code correspondant à
          l'évaluation de la condition. *)
       b test_label
       (* Bloc de code pour le corps de la boucle, précédé de son étiquette. *)
       @@ label code_label
       @@ tr_seq s
       (* À la fin d'un tour de boucle on passe à l'évaluation de la condition 
          de la boucle, pour déterminer s'il faut faire un nouveau tour. *)
       @@ label test_label
       @@ tr_expr c
       (* Si la condition est non nulle, alors on revient quelques lignes
          plus haut, au début du corps de la boucle. *)
       @@ bnez t0 code_label
       (* Sinon on passe à la suite, en l'occurrence justement le code associé 
          à l'instruction suivant la boucle. *)
       (* Note : si on n'avait pas placé l'instruction [b test_label] au
          début, on aurait obtenu le comportement d'une boucle do-while
          plutôt que while. *)

    (* Terminaison d'une fonction. *)
    | Return(e) ->
       (* Évaluation de la valeur à renvoyer, placée dans $t0 *)
       tr_expr e
       (* Désallocation de la partie de la pile utilisée pour les variables
          locales. *)
       @@ move sp fp
       (* Récupération de l'adresse de retour *)
       @@ lw ra (-4) fp
       (* Restauration du pointeur de référence de l'appelant *)
       @@ lw fp 0 fp
       (* On repasse la main à l'appelant *)
       @@ jr ra

    (* Expression utilisée comme une instruction.
       Notez que le code MIPS généré écrit une valeur dans $t0, mais
       celle-ci ne sera pas utilisée. *)
    | Expr(e) ->
       tr_expr e

            
  in

  (**
     Code généré pour la fonction.
     Rappel : au moment où ce code prend la main, les arguments ont
     déjà été évalués et placés sur la pile. La moitié du tableau
     d'activation est donc déjà construite et il va maintenant falloir
     construire sa deuxième moitié.
   *)
  (* Sauvegarde de l'adresse de référence du tableau d'activation de
     l'appelant et de l'adresse de retour. *)
  push fp
  @@ push ra
  (* Définition de l'adresse de référence du nouveau tableau. *)
  @@ addi fp sp 8
  (* Pour s'assurer que l'espace destiné aux variables locales ne sera
     pas utilisé, on décale le pointeur indiquant le sommet de la pile. *)
  @@ addi sp sp (-4 * List.length fdef.locals)
  (* Après ce préambule, on peut passer le relais au "vrai" code de la 
     fonction. *)
  @@ tr_seq fdef.code
  (* Si l'exécution arrive au bout de ce cette séquence, c'est qu'on n'a pas 
     croisé d'instruction [return]. On inclut ici un fragment de code MIPS
     correspondant à [return 0;]. *)
  @@ li t0 0
  @@ move sp fp
  @@ lw ra (-4) fp
  @@ lw fp 0 fp
  @@ jr ra

(**
   Fonction principale de traduction d'un programme.
 *)
let translate_program prog =
  (* Fragment de code MIPS destiné à être placé au début du programme
     assembleur généré, pour récupérer l'éventuel argument entier passé
     sur la ligne de commande, puis passer la main à la fonction "main". *)
  let init =
    (* Au début, $a0 contient le nombre d'arguments passés en ligne de 
       commande. Si ce nombre est 0, on saute les deux lignes suivantes. *)
    beqz a0 "init_end"
    (* Sinon, $a1 contient l'adresse d'un tableau de chaînes de caractères
       contenant les arguments passés en ligne de commande.
       Ici, on suppose qu'il n'y a qu'un argument, on place l'adresse de la
       chaîne correspondante dans $a0 et on appelle une fonction auxiliaire 
       "atoi" définie plus bas pour transformer la chaîne en un entier. *)
    @@ lw a0 0 a1
    @@ jal "atoi"
    @@ label "init_end"
    (* À la fin, l'entier décodé est dans $v0. On le place sur la pile et
       on appelle la fonction "main". *)
    @@ push v0
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
      label fdef.name @@ tr_function fdef @@ code)
    prog.functions nop
  in
  (* On commence par le code d'initialisation vu plus haut, puis on place en
     vrac le code généré pour chaque fonction. *)
  let text = init @@ function_codes @@ built_ins
  (* Dans la partie "données", on introduit une étiquette pour chaque variable
     globale. Chaque variable globale est initialisée à 0. *)
  and data = List.fold_right
    (fun id code -> label id @@ dword [0] @@ code)
    prog.globals nop
  in
  
  { text; data }
