include Formula
open Formula
open Dimacs
(* include Formula *)
(* include Dimacs *)

let test_cnf = load "/Users/brodylittle/Git/ocaml_sat/test/aim-100-1_6-no-1.cnf"
let load = load

type status = Sat | Unsat [@@deriving show] 

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
      (* print_endline @@ "Hit unit prop with" ^ c; *)
      let assignment = (c, true) in
      Some (clauses |> List.filter_map @@ simplify assignment)
  | Some (Neg c) ->
      (* print_endline @@ "Hit unit prop with" ^ c; *)
      let assignment = (c, false) in
      Some (clauses |> List.filter_map @@ simplify assignment)

(* This is optional *)
let literal_elim clauses =
  let pures = pure_literals clauses in
  (* print_endline ("Pure literals found: " ^ (String.concat ", " (List.map show_literal pures))); *)
  match List.nth_opt pures 0 with
  | None -> None
  | Some (Pos c) ->
  (* print_endline "Hit literal elimination"; *)
      let assignment = (c, true) in
      Some (clauses |> List.filter_map @@ simplify assignment)
  | Some (Neg c) ->
  (* print_endline "Hit literal elimination"; *)
      let assignment = (c, false) in
      Some (clauses |> List.filter_map @@ simplify assignment)

let choose_variable clauses =
  (* Choose first variable that appears in both positive and negative form *)
  let all_vars = literals clauses in
  List.find_opt (fun var ->
    let pos_exists = clauses |> List.exists (List.mem (Pos var)) in
    let neg_exists = clauses |> List.exists (List.mem (Neg var)) in
    pos_exists && neg_exists
  ) all_vars

let resolve_on_variable var clauses =
  (* print_endline "hit resolution"; *)
  let pos_clauses = clauses |> List.filter (List.mem (Pos var)) in
  let neg_clauses = clauses |> List.filter (List.mem (Neg var)) in
  let other_clauses = clauses |> List.filter (fun c -> 
    not (List.mem (Pos var) c || List.mem (Neg var) c)) in
  
  let resolved_clauses = 
    List.fold_left (fun acc pos_clause ->
      List.fold_left (fun acc2 neg_clause ->
        let pos_without_var = List.filter ((<>) (Pos var)) pos_clause in
        let neg_without_var = List.filter ((<>) (Neg var)) neg_clause in
        let combined = pos_without_var @ neg_without_var in
        let deduped = List.sort_uniq compare combined in
        
        let is_tautology = List.exists (fun lit ->
          List.mem (match lit with Pos v -> Neg v | Neg v -> Pos v) deduped
        ) deduped in
        
        if is_tautology then acc2 else deduped :: acc2
      ) acc neg_clauses
    ) [] pos_clauses
  in
  resolved_clauses @ other_clauses

let resolve clauses =
  match choose_variable clauses with
  | None -> clauses 
  | Some var -> 
    (* print_endline @@ "Hit resolution with " ^ var; *)
    resolve_on_variable var clauses

let has_empty_clause = List.exists List.is_empty

let rec dp (clauses : clause_set) =
  (* print_endline @@ show_clause_set clauses; *)
  if List.is_empty clauses then Sat
  else if has_empty_clause clauses then Unsat
  else
    match unit_prop clauses with
    | Some cs -> dp cs
    | None -> (
        match literal_elim clauses with
        | Some cs -> dp cs
        | None ->
            let resolved = resolve clauses in
            if resolved = clauses then
              failwith "No progress in resolution - algorithm stuck"
            else dp resolved)

let sat f = load f |> dp
