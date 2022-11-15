(**
   La traduction de MIMP vers AIMP réalise deux tâches principales
   - explosion des expressions en séquences d'instructions atomiques,
     en introduisant au passage des registres virtuels pour stocker les
     résultats intermédiaires des calcules
   - implémentation des conventions de passage des paramètres et résultats
     des fonctions, ainsi que des conventions de sauvegarde des registres
     physiques

   Conventions à réaliser :
   - pour la transmission des résultats : registre $v0
   - pour le passage des paramètres, AU CHOIX
     * soit tout sur la pile (premier paramètre au sommets, les suivante
       en progressant vers l'intérieur de la pile)
     * soit les quatre premiers dans les $ai, puis les suivants sur la
       pile
   - lors d'un appel de fonction, l'appelant doit gérer la sauvegarde des
     registres $ti, $ai et $v0, et l'appelé doit gérer la sauvegarde des
     registres $si

   La création des registres virtuels est faite indépendamment pour chaque
   fonction. Dans une fonction donnée, les registres virtuels sont vus
   comme des variables locales.
 *)

open Aimp

let popr r =
  (* Retourne la séquence qui Pop le haut de la pile dans r *)
  Nop ++ Read(r, "$sp") ++ Pop(1)

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
    name
  in

  let local r = List.mem r !vregs in
  let param r = List.mem r fdef.params in
  let global r = not (local r) && not (param r) in

  (* Fonction de traduction des expressions.
     Renvoie une paire (r, s) d'une séquence s et du nom r du registre
     virtuel contenant la valeur de l'expression. *)
  let rec tr_expr = function
    | Mimp.Cst n ->
      let r = new_vreg() in r, Nop ++ Cst(r, n)
    | Mimp.Bool b -> 
      let r = new_vreg() in 
      let n = if b then 1 else 0 in
      r, Nop ++ Cst(r, n)
    | Mimp.Var x ->
      (* Il faut distinguer ici entre variables locales, paramètres et
          variables globales. TODO ? *)
      if local x then
        (* On considère que les variables sont déjà des vregs *)
        x, Nop
      else if global x then
        let r = new_vreg() in r, Nop ++ Read(r, x)
      else if param x then
        x, Nop
      else
        failwith "damn son"
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
      let sarg = List.fold_left (fun sarg e -> let r, s = tr_expr e in sarg @@ s ++ Push(r)) Nop args in
      "$v0", sarg ++ Call(f, List.length args)
  in

  let rec tr_instr = function
    | Mimp.Putchar e ->
      let r, s = tr_expr e in
      s ++ Putchar r
    | Mimp.Set(x, e) ->
      if local x then 
        match e with
        | Cst n -> 
            Nop ++ Cst(x, n)
        | Binop(op, e1, e2) ->
            let r1, s1 = tr_expr e1 in let r2, s2 = tr_expr e2 in
            s1 @@ s2 ++ Binop(x, tr_binop op, r1, r2)
        | Unop(Addi n, e) ->
            let r, s = tr_expr e in
            s ++ Unop(x, Addi n, r)
        | _ -> 
            let r, s = tr_expr e in s ++ Move(x, r)
      else if global x then
        let r, s = tr_expr e in s ++ Write(x, r)
      else if param x then
        let r, s = tr_expr e in s ++ Move(x, r)
      else
        failwith "damn son"
    | Mimp.If(e, s1, s2) ->
        let r, s = tr_expr e in s ++ If(r, tr_seq s1, tr_seq s2)
    | Mimp.While(e, s) ->
        let r, s' = tr_expr e in Nop ++ While(s', r, tr_seq s)
    | Mimp.Return e ->
       let r, s = tr_expr e in s ++ Move("$v0", r) ++ Return
    | Mimp.Expr e ->
       let r, s = tr_expr e in s
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
