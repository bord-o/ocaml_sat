include Formula
open Formula
open Dimacs
(* include Formula *)
(* include Dimacs *)

let test_cnf = load "/Users/brodylittle/Git/ocaml_sat/test/aim-100-1_6-no-1.cnf"
let load = load

type status = Sat | Unsat [@@deriving show] 

(*
  Go through clauses
  If P = true:
    Remove all clauses containing Pos "P" (they're satisfied)
    Remove Neg "P" from all other clauses (it becomes false)
  If P = false:
    Remove all clauses containing Neg "P" (they're satisfied)
    Remove Pos "P" from all other clauses (it becomes false)
*)
(* return None if it should be removed, otherwise remove P and return some List *)

type assignment = string * bool

let simplify ((v, assign) : assignment) (clause : clause) =
  if assign && clause |> List.mem (Pos v) then None
  else if (not assign) && clause |> List.mem (Neg v) then None
  else
    let simplified =
      clause
      |> List.filter_map @@ fun p ->
         match p with
         | Pos a -> if a = v && not assign then None else Some (Pos a)
         | Neg a -> if a = v && assign then None else Some (Neg a)
    in
    Some simplified

(* None means that there were no unit clauses, a result means they have been simplified *)
let unit_prop clauses =
  let is_unit : clause -> literal option = function
    | [ p ] -> Some p
    | _ -> None
  in
  let rec first_unit_opt : clause_set -> literal option = function
    | [] -> None
    | p :: ps -> (
        match is_unit p with None -> first_unit_opt ps | Some p' -> Some p')
  in
  match first_unit_opt clauses with
  | None -> None
  | Some (Pos c) ->
      print_endline @@ "Hit unit prop with" ^ c;
      let assignment = (c, true) in
      Some (clauses |> List.filter_map @@ simplify assignment)
  | Some (Neg c) ->
      print_endline @@ "Hit unit prop with" ^ c;
      let assignment = (c, false) in
      Some (clauses |> List.filter_map @@ simplify assignment)

(* This is optional *)
let literal_elim clauses =
  let pures = pure_literals clauses in
  match List.nth_opt pures 0 with
  | None -> None
  | Some (Pos c) ->
  print_endline "Hit literal elimination";
      let assignment = (c, true) in
      Some (clauses |> List.filter_map @@ simplify assignment)
  | Some (Neg c) ->
  print_endline "Hit literal elimination";
      let assignment = (c, false) in
      Some (clauses |> List.filter_map @@ simplify assignment)

let resolve clauses =
  let pures = pure_literals clauses in
  let resolv_var =
    clauses
    |> List.find_map @@ fun c ->
       List.find_opt (fun var -> not (pures |> List.mem var )) c
  in
  match resolv_var with
  | None -> clauses
  (* Need to find two clauses with opposing vars and combine them, removing our var and its negation *)
  | Some v ->
    let res = clauses |> List.find_opt @@ fun clause -> clause |> List.exists @@ fun var -> same_sign v var in
    let opp = clauses |> List.find_opt @@ fun clause -> clause |> List.exists @@ fun var -> opposite_sign v var in
    match res, opp with
    | Some r, Some o ->
      print_endline @@ "Hit resolution with " ^ (name v);
      let combined = r @ o |> List.filter @@ fun rv -> not (name rv = name v) in
      combined :: clauses |> List.filter @@ fun c -> c <> r && c <> o
    | _, _ -> failwith "couldn't resolve"

let has_empty_clause = List.exists List.is_empty

let rec dp (clauses : clause_set) =
  print_endline @@ show_clause_set clauses;
  ignore @@ read_line ();
  match unit_prop clauses with
  | Some cs -> dp cs
  | None -> (
      (* match literal_elim clauses with *)
      (* | Some cs -> dp cs *)
      (* | None -> *)
          if List.is_empty clauses then Sat
          else if has_empty_clause clauses then Unsat
          else dp (resolve clauses))

let sat f = load f |> dp
