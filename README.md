# ocaml_sat

## Terms

Literal: a variable or its negation

Clause: disjunction of literals

Formula(CNF): a conjunction of clauses

Interpretation: a combination of variable assignments

## DP Algorithm

Based on three concepts, repeatedly applied against a clause set.

- Unit propagation
  - For a unit clause, say P, we remove all clauses containing P and we remove ~P from any clauses
- Pure literal elimination (optional)
  - For any variable that appears only positive or only negative, assign it to true or false respectively
- Resolution 
  - Find two clauses, one containing a variable, say P, and the other, ~P. We combine these clauses by removing P and OR'ing everything together

## TODO

[ x ] Function for converting internal representation into CNF
[ x ] Function for parsing dimac files into internal representation (already in CNF tho)
[ x ] Function to evaluate a formula given an interpretation
[ ] Implementation of DP 
