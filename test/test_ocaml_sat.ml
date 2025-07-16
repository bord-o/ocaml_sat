
open Sat


let show_binding = function
    `A -> "A "
    | `B -> "B "
    | `C -> "C "
    | `D -> "D "
let pp_binding (_f: Format.formatter) b = print_string  (show_binding b)

(* Basic atoms - should remain unchanged *)
let test1_input = !!`A
let%expect_test "basic atom" = 
    let o = nnf test1_input in
    print_endline (show_normalized pp_binding o);
    [%expect {||}]

(* Double negation elimination *)
let test2_input = neg (neg !!`A)

(* Single negation of atom - should remain *)
let test3_input = neg !!`A

(* De Morgan's law: ¬(A ∧ B) = ¬A ∨ ¬B *)
let test4_input = neg (!!`A &&& !!`B)

(* De Morgan's law: ¬(A ∨ B) = ¬A ∧ ¬B *)
let test5_input = neg (!!`A ||| !!`B)

(* Implication: A → B = ¬A ∨ B *)
let test6_input = !!`A --> !!`B

(* Equivalence: A ↔ B = (¬A ∨ B) ∧ (A ∨ ¬B) *)
let test7_input = !!`A === !!`B

(* Nested implication: A → (B → C) = ¬A ∨ (¬B ∨ C) *)
let test8_input = !!`A --> (!!`B --> !!`C)

(* Complex nested: ¬(A → B) = ¬(¬A ∨ B) = A ∧ ¬B *)
let test9_input = neg (!!`A --> !!`B)

(* Equivalence with negation: ¬(A ↔ B) should become (A ∧ B) ∨ (¬A ∧ ¬B) *)
let test10_input = neg (!!`A === !!`B)

(* Mixed operations: (A ∧ B) ∨ (C → D) *)
let test11_input = (!!`A &&& !!`B) ||| (!!`C --> !!`D)

(* Triple negation: ¬¬¬A = ¬A *)
let test12_input = neg (neg (neg !!`A))

(* Conjunction and disjunction should pass through unchanged *)
let test13_input = !!`A &&& !!`B

let test14_input = !!`A ||| !!`B

(* Complex nested equivalence: (A ∧ B) ↔ (C ∨ D) *)
let test15_input = (!!`A &&& !!`B) === (!!`C ||| !!`D)
