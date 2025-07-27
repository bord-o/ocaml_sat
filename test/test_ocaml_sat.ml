(* open Sat *)
open Sat

let test1 = [[Pos "A"; Pos "B"; Neg "C"]]

let%expect_test "unit_prop with not unit clauses" =
  let u = unit_prop test1 in
  Format.pp_print_option ~none:(fun fmt () -> Format.pp_print_string fmt "None") (pp_clause_set) Format.std_formatter u;
  [@expect {||}]  

let test2 = [[Pos "A"; Pos "B"; Neg "C"]; [Pos "B"]]

let%expect_test "unit_prop with a unit clause" =
  let u = unit_prop test2 in
  Format.pp_print_option ~none:(fun fmt () -> Format.pp_print_string fmt "None") (pp_clause_set) Format.std_formatter u;
  [@expect {||}]  
