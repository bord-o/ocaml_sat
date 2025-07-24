(* open Sat *)

(* let test6_input = !!"P" ||| !!"Q" &&& !!"R" --> neg !!"S" *)

(* let%expect_test "test extract2" = *)
  (* let l = tseytin test6_input in *)
  (* pp_tagged (fun _ a -> pp_tagged  (fun _ _ -> print_newline ()) Format.std_formatter a)  Format.std_formatter l; *)



  (* [%expect *)
    (* {| `Conj ((`Dis ((`Atom (P), `Atom (Q))), `Imp ((`Atom (R), `Neg (`Atom (S)))))) |}] *)
