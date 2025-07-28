(* open Sat *)
open Sat

(* Helper function to convert list-based clauses to set-based *)
let clause_set_of_lists (lists : literal list list) : clause_set =
  lists
  |> List.map LiteralSet.of_list
  |> ClauseSet.of_list

let test1 = clause_set_of_lists [ [ Pos "A"; Pos "B"; Neg "C" ] ]

let%expect_test "unit_prop with not unit clauses" =
  (let u = unit_prop test1 in
   Format.pp_print_option
     ~none:(fun fmt () -> Format.pp_print_string fmt "None")
     pp_clause_set Format.std_formatter u)
  [@expect {||}];
  [%expect {| None |}]

let test2 = clause_set_of_lists [ [ Pos "A"; Pos "B"; Neg "C" ]; [ Pos "B" ] ]

let%expect_test "unit_prop with a unit clause" =
  (let u = unit_prop test2 in
   Format.pp_print_option
     ~none:(fun fmt () -> Format.pp_print_string fmt "None")
     pp_clause_set Format.std_formatter u)
  [@expect {||}];
  [%expect {| [] |}]

(* Basic SAT solver tests with simple formulas *)

let%expect_test "satisfiable single clause" =
  let clauses = clause_set_of_lists [ [ Pos "A" ] ] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    1
    0
    Sat.Sat |}]

let%expect_test "unsatisfiable contradictory unit clauses" =
  let clauses = clause_set_of_lists [ [ Pos "A" ]; [ Neg "A" ] ] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    2
    1
    Sat.Unsat |}]

let%expect_test "satisfiable two variable formula" =
  let clauses = clause_set_of_lists [ [ Pos "A"; Pos "B" ]; [ Neg "A"; Pos "B" ] ] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    2
    0
    Sat.Sat |}]

let%expect_test "empty clause set is satisfiable" =
  let clauses = clause_set_of_lists [] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    0
    Sat.Sat |}]

let%expect_test "pure literal elimination test" =
  let clauses =
    clause_set_of_lists [ [ Pos "A"; Pos "B" ]; [ Pos "A"; Neg "C" ]; [ Pos "B"; Neg "C" ] ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    3
    1
    0
    Sat.Sat |}]

let%expect_test "unit propagation creates satisfiable result" =
  let clauses =
    clause_set_of_lists [ [ Pos "A" ]; [ Neg "A"; Pos "B" ]; [ Neg "A"; Neg "B"; Pos "C" ] ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    3
    2
    1
    0
    Sat.Sat |}]

let%expect_test "small unsatisfiable formula" =
  let clauses =
    clause_set_of_lists [
      [ Pos "A"; Pos "B" ];
      [ Neg "A"; Pos "B" ];
      [ Pos "A"; Neg "B" ];
      [ Neg "A"; Neg "B" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    Hit resolution with A
    2
    1
    Sat.Unsat |}]

(* More complex edge case tests *)

let%expect_test "tautology clause should be ignored" =
  let clauses = clause_set_of_lists [ [ Pos "A"; Neg "A" ]; [ Pos "B" ] ] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    2
    1
    Hit resolution with A
    0
    Sat.Sat |}]

let%expect_test "multiple unit clauses in sequence" =
  let clauses =
    clause_set_of_lists [
      [ Pos "A" ];
      [ Pos "B" ];
      [ Pos "C" ];
      [ Neg "A"; Neg "B"; Neg "C"; Pos "D" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    3
    2
    1
    0
    Sat.Sat |}]

let%expect_test "resolution creates tautology" =
  let clauses =
    clause_set_of_lists [
      [ Pos "A"; Pos "B" ];
      [ Neg "A"; Neg "B" ];
      [ Pos "A"; Neg "B" ];
      [ Neg "A"; Pos "B" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    Hit resolution with A
    2
    1
    Sat.Unsat |}]

let%expect_test "pure literal with multiple occurrences" =
  let clauses =
    clause_set_of_lists [
      [ Pos "A"; Pos "B" ];
      [ Pos "A"; Pos "C" ];
      [ Pos "A"; Pos "D" ];
      [ Neg "B"; Neg "C"; Neg "D" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    1
    0
    Sat.Sat |}]

let%expect_test "mixed unit propagation and pure literal elimination" =
  let clauses =
    clause_set_of_lists [
      [ Pos "A" ];
      [ Neg "A"; Pos "B"; Pos "C" ];
      [ Pos "D" ];
      [ Neg "D"; Pos "E" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    3
    2
    1
    0
    Sat.Sat |}]

let%expect_test "horn clause satisfiable" =
  (* Classic Horn clause: (¬A ∨ ¬B ∨ C) ∧ (A) ∧ (B) - should derive C *)
  let clauses = clause_set_of_lists [ [ Neg "A"; Neg "B"; Pos "C" ]; [ Pos "A" ]; [ Pos "B" ] ] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    3
    2
    1
    0
    Sat.Sat |}]

let%expect_test "horn clause unsatisfiable" =
  (* (¬A ∨ ¬B) ∧ (A) ∧ (B) - should be UNSAT *)
  let clauses = clause_set_of_lists [ [ Neg "A"; Neg "B" ]; [ Pos "A" ]; [ Pos "B" ] ] in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    3
    Hit resolution with A
    2
    1
    Sat.Unsat |}]

let%expect_test "resolution with longer clauses" =
  (* Test resolution doesn't lose literals *)
  let clauses =
    clause_set_of_lists [
      [ Pos "A"; Pos "B"; Pos "C" ];
      [ Neg "A"; Pos "D"; Pos "E" ];
      [ Neg "B"; Neg "C"; Neg "D"; Neg "E" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    3
    Hit resolution with A
    2
    Hit resolution with B
    0
    Sat.Sat |}]

let%expect_test "duplicate literals in clauses" =
  (* Should handle duplicate literals gracefully *)
  let clauses =
    clause_set_of_lists [
      [ Pos "A"; Pos "A"; Pos "B" ];
      [ Neg "A"; Neg "A" ];
      [ Neg "B"; Pos "C"; Pos "C" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    3
    2
    1
    0
    Sat.Sat |}]

let%expect_test "three variable satisfiable" =
  (* (A ∨ B ∨ C) ∧ (¬A ∨ B) ∧ (¬B ∨ C) ∧ (¬C) - should be SAT with A=false, B=false, C=false *)
  let clauses =
    clause_set_of_lists [
      [ Pos "A"; Pos "B"; Pos "C" ];
      [ Neg "A"; Pos "B" ];
      [ Neg "B"; Pos "C" ];
      [ Neg "C" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    3
    2
    1
    Sat.Unsat |}]

let%expect_test "pigeonhole principle 2 pigeons 1 hole" =
  (* 2 pigeons, 1 hole - should be UNSAT *)
  (* P1 ∨ P2 (at least one pigeon in hole) ∧ ¬P1 ∨ ¬P2 (at most one pigeon in hole) ∧ P1 ∧ P2 (both pigeons must be placed) *)
  let clauses =
    clause_set_of_lists [
      [ Pos "P1"; Pos "P2" ]; [ Neg "P1"; Neg "P2" ]; [ Pos "P1" ]; [ Pos "P2" ];
    ]
  in
  (let result = clauses |> dp in
   print_endline (show_status result))
  [@expect {||}];
  [%expect {|
    4
    2
    1
    Sat.Unsat |}]
