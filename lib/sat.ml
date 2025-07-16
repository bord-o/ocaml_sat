type status = Sat | Unsat

type 'a formula =
  | Conj of 'a formula * 'a formula
  | Dis of 'a formula * 'a formula
  | Neg of 'a formula
  | Imp of 'a formula * 'a formula
  | Eq of 'a formula * 'a formula
  | Atom of 'a
[@@deriving show, map, fold]

type form = 
    Nnf of bool
    | Cnf of bool
    | Predicate of bool

let ( &&& ) x y = Conj (x, y)
let ( ||| ) x y = Dis (x, y)
let ( --> ) x y = Imp (x, y)
let ( === ) x y = Eq (x, y)
let ( !! ) x = Atom x
let neg x = Neg x
let test = !!`A &&& !!`B
let ( let* ) = Result.bind

let rec eval (form : 'a formula) (interp : ('a * bool) list) =
  let eval' f = eval f interp in
  match form with
  | Conj (l, r) ->
      let* l_val = eval' l in
      let* r_val = eval' r in
      Ok (l_val && r_val)
  | Dis (l, r) ->
      let* l_val = eval' l in
      let* r_val = eval' r in
      Ok (l_val || r_val)
  | Neg f ->
      let* val' = eval' f in
      Ok (not val')
  | Imp (l, r) -> eval' (neg l ||| r)
  | Eq (l, r) -> eval' (neg l ||| r &&& (l ||| neg r))
  | Atom v -> interp |> List.assoc_opt v |> Option.to_result ~none:`Unbound

let rec cnf (form : form formula) = ()
