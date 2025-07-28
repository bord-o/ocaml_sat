open Formula

let to_formula (dimacs : int list list) =
  dimacs
  |> List.map (fun raw_clause ->
         raw_clause
         |> List.map (fun variable_idx ->
                if variable_idx < 0 then
                  Neg (string_of_int (Int.neg variable_idx))
                else Pos (string_of_int variable_idx)))

let load filename =
  try
    let infile = open_in filename in
    let file_content = really_input_string infile (in_channel_length infile) in
    let filebuf = Lexing.from_string file_content in
    let absyn = Parser.main Lexer.read filebuf in
    close_in infile;
    absyn |> to_formula
  with e ->
    print_endline @@ Printexc.to_string e;
    failwith "err"
