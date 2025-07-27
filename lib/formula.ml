(* This type represents a normal propositional logic formula *)
type 'a formula =
  [ `Conj of 'a formula * 'a formula
  | `Dis of 'a formula * 'a formula
  | `Neg of 'a formula
  | `Imp of 'a formula * 'a formula
  | `Eq of 'a formula * 'a formula
  | `Atom of 'a ]
[@@deriving show]

type literal =
  | Pos of string [@printer fun fmt s -> Format.pp_print_string fmt s]
  | Neg of string [@printer fun fmt s -> Format.pp_print_string fmt ("¬"^s)] [@@deriving show]

let name = function Pos n -> n | Neg n -> n
let opposite_sign  a b = match a, b with
  | Pos m, Neg n when m = n -> true
  | Neg m, Pos n when m = n -> true
  | _ -> false
let same_sign a b = match a, b with
  | Pos m, Pos n when m = n -> true
  | Neg m, Neg n when m = n -> true
  | _ -> false

type clause = literal list [@@deriving show]
type clause_set = clause list [@@deriving show]

let ( &&& ) x y = `Conj (x, y)
let ( ||| ) x y = `Dis (x, y)
let ( --> ) x y = `Imp (x, y)
let ( === ) x y = `Eq (x, y)
let ( !! ) x = `Atom x
let neg x = `Neg x
let test = !!`A &&& !!`B
let ( let* ) = Result.bind
let test_input = neg (!!"P" ||| (!!"Q" &&& neg !!"R"))

let rec eval_interp (form : 'a formula) (interp : ('a * bool) list) =
  let eval' f = eval_interp f interp in
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

let tseytin (form : string formula) : clause_set =
  let name_counter = ref 0 in
  let sub_name () =
    let name = "p_" ^ string_of_int !name_counter in
    incr name_counter;
    name
  in

  let rec tag = function
    | `Neg a -> `Neg (sub_name (), tag a)
    | `Dis (a, b) -> `Dis (sub_name (), tag a, tag b)
    | `Eq (a, b) -> `Eq (sub_name (), tag a, tag b)
    | `Conj (a, b) -> `Conj (sub_name (), tag a, tag b)
    | `Imp (a, b) -> `Imp (sub_name (), tag a, tag b)
    | `Atom _ as a -> a
  in
  let get_tag = function
    | `Neg (t, _) -> t
    | `Dis (t, _, _) -> t
    | `Eq (t, _, _) -> t
    | `Conj (t, _, _) -> t
    | `Imp (t, _, _) -> t
    | `Atom t -> t
  in
  let child_tags l r =
    let b = get_tag l in
    let c = get_tag r in
    (b, c)
  in
  let rec acc_clauses = function
    | `Neg (a, child) ->
        let a = a in
        let b = get_tag child in
        [ [ Neg a; Neg b ]; [ Pos a; Pos b ] ] @ acc_clauses child
    | `Conj (a, l_child, r_child) ->
        let a = a in
        let b, c = child_tags l_child r_child in
        [ [ Neg a; Pos b ]; [ Neg a; Pos c ]; [ Neg b; Neg c; Pos a ] ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Dis (a, l_child, r_child) ->
        let a = a in
        let b, c = child_tags l_child r_child in
        [ [ Neg a; Pos b; Pos c ]; [ Neg b; Pos a ]; [ Neg c; Pos a ] ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Eq (a, l_child, r_child) ->
        let a = a in
        let b, c = child_tags l_child r_child in
        [
          [ Neg a; Neg b; Pos c ];
          [ Neg a; Pos b; Neg c ];
          [ Pos a; Neg b; Neg c ];
          [ Pos a; Pos b; Pos c ];
        ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Imp (a, l_child, r_child) ->
        let a = a in
        let b, c = child_tags l_child r_child in
        [ [ Neg a; Neg b; Pos c ]; [ Pos a; Pos b ]; [ Pos a; Neg c ] ]
        @ acc_clauses l_child @ acc_clauses r_child
    | `Atom _ -> []
  in
  let tagged = tag form in
  let clauses = acc_clauses tagged in
  clauses

let rec disjunct ~clauses =
  match clauses with
  | [] -> failwith "Empty"
  | [ c ] -> c
  | c :: clauses -> `Dis (c, disjunct ~clauses)

let rec conjunct ~clauses =
  match clauses with
  | [] -> failwith "Empty"
  | [ c ] -> c
  | c :: clauses -> `Conj (c, conjunct ~clauses)

let variables form =
  let tbl = Hashtbl.create 100 in
  let rec aux = function
    | `Neg a -> aux a
    | `Dis (a, b) ->
        aux a;
        aux b
    | `Eq (a, b) ->
        aux a;
        aux b
    | `Conj (a, b) ->
        aux a;
        aux b
    | `Imp (a, b) ->
        aux a;
        aux b
    | `Atom a -> Hashtbl.replace tbl a ()
  in
  aux form;
  tbl |> Hashtbl.to_seq_keys |> List.of_seq

let literals (cnf : clause_set) =
  let tbl = Hashtbl.create 100 in
  cnf |> List.flatten
  |> List.iter (fun literal ->
         let res = match literal with Neg c -> c | Pos c -> c in

         Hashtbl.replace tbl res ());
  tbl |> Hashtbl.to_seq_keys |> List.of_seq

let pure_literals (cnf : clause_set) =
  let var_forms = Hashtbl.create 100 in
  cnf |> List.flatten
  |> List.iter (fun literal ->
         let var_name = match literal with Pos v | Neg v -> v in
         let current_forms = Hashtbl.find_opt var_forms var_name |> Option.value ~default:[] in
         Hashtbl.replace var_forms var_name (literal :: current_forms));
  
  let pure_lits = ref [] in
  Hashtbl.iter (fun _var forms ->
    let has_pos = List.exists (function Pos _ -> true | _ -> false) forms in
    let has_neg = List.exists (function Neg _ -> true | _ -> false) forms in
    if has_pos && not has_neg then
      pure_lits := (List.find (function Pos _ -> true | _ -> false) forms) :: !pure_lits
    else if has_neg && not has_pos then
      pure_lits := (List.find (function Neg _ -> true | _ -> false) forms) :: !pure_lits
  ) var_forms;
  !pure_lits
