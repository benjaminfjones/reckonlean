# Poor man's translation of OCaml to Lean 4
#
# Usage:
# $ sed -I orig -f ocaml-to-lean.sed ReckonLean/Dpll.lean

s/(\*/\/-/g
s/\*)/-\//g
s/^let/def/g
s/in$//g
s/=/:=/g
s/->/=>/g

