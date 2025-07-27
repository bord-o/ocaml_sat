%{

%}

%token EOF 
%token <int> INT 
%token ZERO


%start <int list list> main

%%

(* -------------------------------------------------------------------------- *)

(* We wish to parse an expression followed with an end-of-line. *)

main:
  | lines EOF {$1}

lines:
  | line {[$1]}
  | lines line {$1 @ [$2]}

line:
  ints ZERO {$1}

ints:
  | INT {[$1]}
  | ints INT {$1 @ [$2]}

