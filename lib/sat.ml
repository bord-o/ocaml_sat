type status = Sat | Unsat

type 'a formula =
  [ `Conj of 'a formula * 'a formula
  | `Dis of 'a formula * 'a formula
  | `Neg of 'a formula
  | `Imp of 'a formula * 'a formula
  | `Eq of 'a formula * 'a formula
  | `Atom of 'a ]
[@@deriving show]

type 'a normalized =
  [ `Conj of 'a normalized * 'a normalized
  | `Dis of 'a normalized * 'a normalized
  | `Neg of 'a normalized
  | `Atom of 'a ]
[@@deriving show]

let ( &&& ) x y = `Conj (x, y)
let ( ||| ) x y = `Dis (x, y)
let ( --> ) x y = `Imp (x, y)
let ( === ) x y = `Eq (x, y)
let ( !! ) x = `Atom x
let neg x = `Neg x
let test = !!`A &&& !!`B
let ( let* ) = Result.bind

let rec eval (form : 'a formula) (interp : ('a * bool) list) =
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

let rec nnf (form : 'a formula) : 'a normalized =
  match form with
  | `Atom v -> `Atom v
  | `Neg (`Neg (`Atom v)) -> `Atom v
  | `Neg (`Atom _) as n -> n
  | `Neg (`Conj (`Atom a, `Atom b)) -> neg !!a ||| neg !!b
  | `Neg (`Dis (`Atom a, `Atom b)) -> neg !!a &&& neg !!b
  | `Imp (`Atom a, `Atom b) -> neg !!a ||| !!b
  | `Eq (`Atom a, `Atom b) -> neg !!a ||| !!b &&& (!!a ||| neg !!b)
  (* Imp and Eq recur as they could result in negating a non atomic formula *)
  | `Neg (`Conj (a, b)) ->
      let a' = nnf (neg a) in
      let b' = nnf (neg b) in
      a' ||| b'
  | `Neg (`Dis (a, b)) ->
      let a' = nnf (neg a) in
      let b' = nnf (neg b) in
      a' &&& b'
  | `Neg (`Imp (a, b)) -> 
      nnf (a &&& neg b)
  | `Neg (`Eq (a, b)) ->   
      nnf ((a &&& neg b) ||| (neg a &&& b))
  | `Neg v ->
      let v' = nnf v in
      neg v'
  | `Imp (a, b) ->
      let a' = nnf a in
      let b' = nnf b in
      let n : 'a formula = (neg a' ||| b' : 'a normalized :> 'a formula) in
      nnf n
  | `Eq (a, b) ->
      let a' = nnf a in
      let b' = nnf b in
      let n : 'a formula =
        (neg a' ||| b' &&& (a' ||| neg b') : 'a normalized :> 'a formula)
      in
      nnf n
      (* Everything else is just a map *)
  | `Dis (a, b) ->
      let a' = nnf a in
      let b' = nnf b in
      a' ||| b'
  | `Conj (a, b) ->
      let a' = nnf a in
      let b' = nnf b in
      a' &&& b'
