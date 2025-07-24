type status = Sat | Unsat

(* This type represents a normal propositional logic formula *)
type 'a formula =
  [ `Conj of 'a formula * 'a formula
  | `Dis of 'a formula * 'a formula
  | `Neg of 'a formula
  | `Imp of 'a formula * 'a formula
  | `Eq of 'a formula * 'a formula
  | `Atom of 'a ]
[@@deriving show]

(* This type represents a formula that is in CNF *)
type 'a normalized =
  [ `Conj of 'a normalized * 'a normalized
  | `Dis of 'a normalized * 'a normalized
  | `Neg of 'a normalized
  | `Atom of 'a ]
[@@deriving show]

type 'a tagged =
  [> `Atom of string
  | `Conj of string * 'a * 'a
  | `Dis of string * 'a * 'a
  | `Eq of string * 'a * 'a
  | `Imp of string * 'a * 'a
  | `Neg of string * 'a ]
  as
  'a
[@@deriving show]

let ( &&& ) x y = `Conj (x, y)
let ( ||| ) x y = `Dis (x, y)
let ( --> ) x y = `Imp (x, y)
let ( === ) x y = `Eq (x, y)
let ( !! ) x = `Atom x
let neg x = `Neg x
let test = !!`A &&& !!`B
let ( let* ) = Result.bind
let test_input = neg (!!"P" ||| (!!"Q" &&& neg !!"R"))

let rec eval form (interp : ('a * bool) list) =
  let eval' f = eval f interp in
  match form with
  | `Conj (l, r) ->
      let* l_val = eval' l in
      let* r_val = eval' r in
      Ok (l_val && r_val)
  | `Dis (l, r) ->
      let* l_val = eval' l in
      let* r_val = eval' r in
      Ok (l_val || r_val)
  | `Neg f ->
      let* val' = eval' f in
      Ok (not val')
  | `Imp (l, r) -> eval' (neg l ||| r)
  | `Eq (l, r) -> eval' (neg l ||| r &&& (l ||| neg r))
  | `Atom v -> interp |> List.assoc_opt v |> Option.to_result ~none:`Unbound

let is_atom = function `Atom _ -> true | _ -> false
let are_atoms a b = is_atom a && is_atom b

(*
  To do this transform, lets tag the 'a in all formulas except the leaves
  with an Atom representing the subformula
 *)
let tseytin (form : 'a formula) =
  let name_counter = ref 0 in
  let sub_name () =
    let name = "p" ^ string_of_int !name_counter in
    incr name_counter;
    name
  in

  let rec tag (f : 'a formula) =
    match f with
    | `Neg a -> `Neg (sub_name (), tag a)
    | `Dis (a, b) -> `Dis (sub_name (), tag a, tag b)
    | `Eq (a, b) -> `Eq (sub_name (), tag a, tag b)
    | `Conj (a, b) -> `Conj (sub_name (), tag a, tag b)
    | `Imp (a, b) -> `Imp (sub_name (), tag a, tag b)
    | `Atom _ as a -> a
  in
  let get_tag (f : 'b tagged) =
    match f with
    | `Neg (t, _) -> t
    | `Dis (t, _, _) -> t
    | `Eq (t, _, _) -> t
    | `Conj (t, _, _) -> t
    | `Imp (t, _, _) -> t
    | `Atom t -> t
  in
  let child_tags l r =
    let b = !!(get_tag l) in
    let c = !!(get_tag r) in
    (b, c)
  in
  let rec acc_clauses (f : 'b tagged) : 'd formula list =
    match f with
    | `Neg (a, child) ->
        let a = !!a in
        let b = !!(get_tag child) in
        [ neg a ||| neg b; a ||| b ] @ acc_clauses child
    | `Conj (a, l_child, r_child) ->
        let a = !!a in
        let b, c = child_tags l_child r_child in
        [ neg a ||| b; neg a ||| c; neg b ||| neg c ||| a ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Dis (a, l_child, r_child) ->
        let a = !!a in
        let b, c = child_tags l_child r_child in
        [ neg a ||| b ||| c; neg b ||| a; neg c ||| a ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Eq (a, l_child, r_child) ->
        let a = !!a in
        let b, c = child_tags l_child r_child in
        [
          neg a ||| neg b ||| c;
          neg a ||| b ||| neg c;
          a ||| neg b ||| neg c;
          a ||| b ||| c;
        ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Imp (a, l_child, r_child) ->
        let a = !!a in
        let b, c = child_tags l_child r_child in
        [ neg a ||| neg b ||| c; a ||| b; a ||| neg c ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Atom _ -> []
  in
  let tagged = tag form in
  let clauses = acc_clauses tagged in
  clauses

