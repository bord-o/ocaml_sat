open Sat

(* Basic atoms - should remain unchanged *)
let test1_input = !!"A"

let%expect_test "basic atom" =
  let o = nnf test1_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Atom (A) |}]

(* Double negation elimination *)
let test2_input = neg (neg !!"A")

let%expect_test "double negation elimination" =
  let o = nnf test2_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Atom (A) |}]

(* Single negation of atom - should remain *)
let test3_input = neg !!"A"

let%expect_test "single negation of atom" =
  let o = nnf test3_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Neg (`Atom (A)) |}]

(* De Morgan's law: ¬(A ∧ B) = ¬A ∨ ¬B *)
let test4_input = neg (!!"A" &&& !!"B")

let%expect_test "De Morgan's law - negation of conjunction" =
  let o = nnf test4_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Dis ((`Neg (`Atom (A)), `Neg (`Atom (B)))) |}]

(* De Morgan's law: ¬(A ∨ B) = ¬A ∧ ¬B *)
let test5_input = neg (!!"A" ||| !!"B")

let%expect_test "De Morgan's law - negation of disjunction" =
  let o = nnf test5_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Conj ((`Neg (`Atom (A)), `Neg (`Atom (B)))) |}]

(* Implication: A → B = ¬A ∨ B *)
let test6_input = !!"A" --> !!"B"

let%expect_test "implication conversion" =
  let o = nnf test6_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Dis ((`Neg (`Atom (A)), `Atom (B))) |}]

(* Equivalence: A ↔ B = (¬A ∨ B) ∧ (A ∨ ¬B) *)
let test7_input = !!"A" === !!"B"

let%expect_test "equivalence conversion" =
  let o = nnf test7_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {|
    `Conj ((`Dis ((`Neg (`Atom (A)), `Atom (B))),
            `Dis ((`Atom (A), `Neg (`Atom (B)))))) |}]

(* Nested implication: A → (B → C) = ¬A ∨ (¬B ∨ C) *)
let test8_input = !!"A" --> (!!"B" --> !!"C")

let%expect_test "nested implication" =
  let o = nnf test8_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Dis ((`Neg (`Atom (A)), `Dis ((`Neg (`Atom (B)), `Atom (C))))) |}]

(* Complex nested: ¬(A → B) = ¬(¬A ∨ B) = A ∧ ¬B *)
let test9_input = neg (!!"A" --> !!"B")

let%expect_test "negation of implication" =
  let o = nnf test9_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Conj ((`Atom (A), `Neg (`Atom (B)))) |}]

(* Equivalence with negation: ¬(A ↔ B) should become (A ∧ B) ∨ (¬A ∧ ¬B) *)
let test10_input = neg (!!"A" === !!"B")

let%expect_test "negation of equivalence" =
  let o = nnf test10_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {|
    `Dis ((`Conj ((`Atom (A), `Neg (`Atom (B)))),
           `Conj ((`Neg (`Atom (A)), `Atom (B))))) |}]

(* Mixed operations: (A ∧ B) ∨ (C → D) *)
let test11_input = !!"A" &&& !!"B" ||| !!"C" --> !!"D"

let%expect_test "mixed operations" =
  let o = nnf test11_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Dis ((`Conj ((`Atom (A), `Atom (B))), `Dis ((`Neg (`Atom (C)), `Atom (D))))) |}]

(* Triple negation: ¬¬¬A = ¬A *)
let test12_input = neg (neg (neg !!"A"))

let%expect_test "triple negation" =
  let o = nnf test12_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Neg (`Atom (A)) |}]

(* Conjunction and disjunction should pass through unchanged *)
let test13_input = !!"A" &&& !!"B"

let%expect_test "conjunction passthrough" =
  let o = nnf test13_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Conj ((`Atom (A), `Atom (B))) |}]

let test14_input = !!"A" ||| !!"B"

let%expect_test "disjunction passthrough" =
  let o = nnf test14_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {| `Dis ((`Atom (A), `Atom (B))) |}]

(* Complex nested equivalence: (A ∧ B) ↔ (C ∨ D) *)
let test15_input = !!"A" &&& !!"B" === (!!"C" ||| !!"D")

let%expect_test "complex nested equivalence" =
  let o = nnf test15_input in
  print_endline (show_normalized Format.pp_print_string o);
  [%expect {|
    `Conj ((`Dis ((`Dis ((`Neg (`Atom (A)), `Neg (`Atom (B)))),
                   `Dis ((`Atom (C), `Atom (D))))),
            `Dis ((`Conj ((`Atom (A), `Atom (B))),
                   `Conj ((`Neg (`Atom (C)), `Neg (`Atom (D)))))))) |}]
