(**
    /[...]/ <=> pas réalisé à cette étape
    x       <=> pas réalisé
    o       <=> réalisé

   La traduction de MIMP vers AIMP réalise deux tâches principales
   o explosion des expressions en séquences d'instructions atomiques,
     en introduisant au passage des registres virtuels pour stocker les
     résultats intermédiaires des calcules
   o implémentation des conventions de passage des paramètres et résultats
     des fonctions, /ainsi que des conventions de sauvegarde des registres
     physiques/

   Conventions à réaliser :
   o pour la transmission des résultats : registre $v0
   o pour le passage des paramètres, AU CHOIX
     x soit tout sur la pile (premier paramètre au sommets, les suivante
       en progressant vers l'intérieur de la pile)
     o soit les quatre premiers dans les $ai, puis les suivants sur la
       pile
   - /lors d'un appel de fonction, l'appelant doit gérer la sauvegarde des
     registres $ti, $ai et $v0, et l'appelé doit gérer la sauvegarde des
     registres $si/

   o La création des registres virtuels est faite indépendamment pour chaque
   fonction. Dans une fonction donnée, les registres virtuels sont vus
   comme des variables locales.
 *)

open Aimp

(* Traduction directe *)
let tr_unop = function
  | Mimp.Addi n -> Addi n
let tr_binop = function
  | Mimp.Add -> Add
  | Mimp.Mul -> Mul
  | Mimp.Lt  -> Lt

(* Fonction principale, de traduction d'une définition de fonction *)
let tr_fdef fdef =
  (* Liste des registres virtuels. Elle est initialisée avec les variables
     locales et sera étendue à chaque création d'un nouveau registre
     virtuel. *)
  let vregs = ref Mimp.(fdef.locals) in
  (* Fonction de génération de nouveaux registres virtuels.
     Renvoie le nouveau nom, et étend la liste. *)
  let counter = ref 0 in
  let new_vreg () =
    let name = Printf.sprintf "#%i" !counter in
    vregs := name :: !vregs;
    incr counter;
    Virtual name
  in

  let mem_local r = List.mem r (!vregs) in
  let mem_param r = List.mem r (fdef.params) in

  (* Fonctions de traduction d'un paramètre : on abstrait le registre
     et la séquence résultants *)
  let tr_param x: reg * sequence = 
    let ip = Tools.index (fdef.params) x in
    (* Les registres des paramètres peuvent être réels ou virtuels. *)
    if ip < 4 then 
      Aimp.to_real "a" ip, Nop 
    else 
      Aimp.Virtual(x), Nop
  in

  (* Fonction de traduction des expressions.
     Renvoie une paire (r, s) d'une séquence s et du nom r du registre
     virtuel contenant la valeur de l'expression. *)
  let rec tr_expr e: reg * sequence = match e with
    | Mimp.Cst n ->
      let r = new_vreg() in 
      r, Nop ++ Cst(r, n)

    | Mimp.Bool b -> 
      let r = new_vreg() in 
      let n = if b then 1 else 0 in
      r, Nop ++ Cst(r, n)

    | Mimp.Var x ->
      if mem_local x then
        (* On considère que les variables sont déjà des vregs *)
        Virtual(x), Nop
      else if mem_param x then
        let r, s = tr_param x in
        r, s
      else
      (* le registre est global *)
        let r = new_vreg() in 
        r, Nop ++ Read(r, x)

    | Mimp.Unop(op, e) ->
      let r1, s1 = tr_expr e in
      let r = new_vreg() in
      r, s1 ++ Unop(r, tr_unop op, r1)

    | Mimp.Binop(op, e1, e2) ->
      let r1, s1 = tr_expr e1 in
      let r2, s2 = tr_expr e2 in
      let r = new_vreg() in
      r, s1 @@ s2 ++ Binop(r, tr_binop op, r1, r2)

    | Mimp.Call(f, args) ->
      (* Il faut réaliser ici la convention d'appel : passer les arguments
        de la bonne manière, et renvoyer le résultat dans $v0. *)
      let counter = ref 0 in
      let sarg = List.fold_left 
        (fun sarg e ->
          incr counter;
          let r, s = tr_expr e in
          if !counter - 1 < Mips.pmax then
            sarg @@ s ++ Move(to_real "a" (!counter - 1), r)
          else
            sarg @@ s ++ Push(r))
        Nop 
        args
      in
      Real("$v0"), 
      Nop 
      (* ATTENTION, dépendant de l'implementation de call dans aimp2eimp et eimp2mips*)
      ++ Call(Mips.lab_callers_save, 0) 
      @@ sarg 
      ++ Call(f, List.length args)
      (* ATTENTION, dépendant de l'implementation de call dans aimp2eimp et eimp2mips*)
      ++ Call(Mips.lab_callers_restore, 0)
  in

  let rec tr_instr inst: sequence = match inst with
    | Mimp.Putchar e ->
      let r, s = tr_expr e in
      s ++ Putchar r

    | Mimp.Set(x, e) ->
      (* Petite ruse ici, rien de méchant : on sait que seul les globales 
         retournent une séquence <> Nop et en plus on obtient la bonne
         traduction de la variable *)
      let r', s' = tr_expr (Mimp.Var x) in
      (match r', s' with
        | Virtual x, Nop (* local ou param *) | Real x, Nop (* param *) ->  
          (match e with
            | Cst n -> 
              Nop ++ Cst(r', n)
            | Binop(op, e1, e2) ->
              let r1, s1 = tr_expr e1 in 
              let r2, s2 = tr_expr e2 in
              s1 @@ s2 ++ Binop(r', tr_binop op, r1, r2)
            | Unop(Addi n, e) ->
              let r, s = tr_expr e in
              s ++ Unop(r', Addi n, r)
            | _ -> 
              let r, s = tr_expr e in 
              s ++ Move(r', r))
        | _, _ -> (* global *)
          let r, s = tr_expr e in 
          s ++ Write(x, r))

    | Mimp.If(e, s1, s2) ->
      let r, s = tr_expr e 
      in s ++ If(r, tr_seq s1, tr_seq s2)
    | Mimp.While(e, s) ->
      let r, s' = tr_expr e in 
      Nop ++ While(s', r, tr_seq s)
    | Mimp.Return e ->
      let r, s = tr_expr e in 
      s ++ Move(Real("$v0"), r) ++ Return
    | Mimp.Expr e ->
      let r, s = tr_expr e in 
      s

  and tr_seq = function
    | []     -> Nop
    | i :: s -> tr_instr i @@ tr_seq s
  in

  let code =
    tr_seq Mimp.(fdef.code)
  in
  {
    name = Mimp.(fdef.name);
    params = Mimp.(fdef.params);
    locals = !vregs;
    code = code
  }

(* Traduction directe *)
let tr_prog p = {
    globals = Mimp.(p.globals);
    functions = List.map tr_fdef Mimp.(p.functions)
  }
