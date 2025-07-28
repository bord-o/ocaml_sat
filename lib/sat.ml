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
  if assign && LiteralSet.mem (Pos v) clause then None
  else if (not assign) && LiteralSet.mem (Neg v) clause then None
  else
    let simplified =
      LiteralSet.fold (fun p acc ->
         match p with
         | Pos a -> if a = v && not assign then acc else LiteralSet.add (Pos a) acc
         | Neg a -> if a = v && assign then acc else LiteralSet.add (Neg a) acc
      ) clause LiteralSet.empty
    in
    Some simplified

(* None means that there were no unit clauses, a result means they have been simplified *)
let unit_prop clauses =
  let first_unit_opt (clauses : clause_set) : literal option =
    try
      let unit_clause = ClauseSet.find_first (fun c -> LiteralSet.cardinal c = 1) clauses in
      Some (LiteralSet.choose unit_clause)
    with Not_found -> None
  in
  match first_unit_opt clauses with
  | None -> None
  | Some (Pos c) ->
      (* print_endline @@ "Hit unit prop with" ^ c; *)
      let assignment = (c, true) in
      let simplified_clauses = ClauseSet.fold (fun clause acc ->
        match simplify assignment clause with
        | None -> acc
        | Some simplified -> ClauseSet.add simplified acc
      ) clauses ClauseSet.empty in
      Some simplified_clauses
  | Some (Neg c) ->
      (* print_endline @@ "Hit unit prop with" ^ c; *)
      let assignment = (c, false) in
      let simplified_clauses = ClauseSet.fold (fun clause acc ->
        match simplify assignment clause with
        | None -> acc
        | Some simplified -> ClauseSet.add simplified acc
      ) clauses ClauseSet.empty in
      Some simplified_clauses

(* This is optional *)
let literal_elim clauses =
  let pures = pure_literals clauses in
  (* print_endline ("Pure literals found: " ^ (String.concat ", " (List.map show_literal pures))); *)
  match List.nth_opt pures 0 with
  | None -> None
  | Some (Pos c) ->
      (* print_endline "Hit literal elimination"; *)
      let assignment = (c, true) in
      let simplified_clauses = ClauseSet.fold (fun clause acc ->
        match simplify assignment clause with
        | None -> acc
        | Some simplified -> ClauseSet.add simplified acc
      ) clauses ClauseSet.empty in
      Some simplified_clauses
  | Some (Neg c) ->
      (* print_endline "Hit literal elimination"; *)
      let assignment = (c, false) in
      let simplified_clauses = ClauseSet.fold (fun clause acc ->
        match simplify assignment clause with
        | None -> acc
        | Some simplified -> ClauseSet.add simplified acc
      ) clauses ClauseSet.empty in
      Some simplified_clauses

let choose_variable clauses =
  (* Choose first variable that appears in both positive and negative form *)
  let all_vars = literals clauses in
  List.find_opt
    (fun var ->
      let pos_exists = ClauseSet.exists (LiteralSet.mem (Pos var)) clauses in
      let neg_exists = ClauseSet.exists (LiteralSet.mem (Neg var)) clauses in
      pos_exists && neg_exists)
    all_vars

let resolve_on_variable var clauses =
  (* print_endline "hit resolution"; *)
  let pos_clauses = ClauseSet.filter (LiteralSet.mem (Pos var)) clauses in
  let neg_clauses = ClauseSet.filter (LiteralSet.mem (Neg var)) clauses in
  let other_clauses =
    ClauseSet.filter (fun c -> not (LiteralSet.mem (Pos var) c || LiteralSet.mem (Neg var) c)) clauses
  in

  let resolved_clauses =
    ClauseSet.fold
      (fun pos_clause acc ->
        ClauseSet.fold
          (fun neg_clause acc2 ->
            let pos_without_var = LiteralSet.remove (Pos var) pos_clause in
            let neg_without_var = LiteralSet.remove (Neg var) neg_clause in
            let combined = LiteralSet.union pos_without_var neg_without_var in

            let is_tautology =
              LiteralSet.exists
                (fun lit ->
                  LiteralSet.mem
                    (match lit with Pos v -> Neg v | Neg v -> Pos v)
                    combined)
                combined
            in

            if is_tautology then acc2 else ClauseSet.add combined acc2)
          neg_clauses acc)
      pos_clauses ClauseSet.empty
  in
  ClauseSet.union resolved_clauses other_clauses

let resolve clauses =
  match choose_variable clauses with
  | None -> clauses
  | Some var ->
      print_endline @@ "Hit resolution with " ^ var;
      resolve_on_variable var clauses

let has_empty_clause = ClauseSet.exists LiteralSet.is_empty

let subsumes clause1 clause2 =
  LiteralSet.subset clause1 clause2

let debug = ref 0

let rec dp (clauses : clause_set) =
  (* if !debug mod 10 = 0 then *)
  print_endline @@ string_of_int @@ ClauseSet.cardinal clauses;
  (* incr debug; *)
  if ClauseSet.is_empty clauses then Sat
  else if has_empty_clause clauses then Unsat
  else
    let clauses =
      ClauseSet.filter
        (fun clause ->
          not
            (ClauseSet.exists
               (fun other -> not (LiteralSet.equal other clause) && subsumes other clause)
               clauses))
        clauses
    in

    match unit_prop clauses with
    | Some cs -> dp cs
    | None -> (
        match literal_elim clauses with
        | Some cs -> dp cs
        | None ->
            let resolved = resolve clauses in
            if ClauseSet.equal resolved clauses then
              failwith "No progress in resolution - algorithm stuck"
            else dp resolved)

let sat f = load f |> dp
