import ReckonLean.Common

/-
/- ------------------------------------------------------------------------- -/
/- Common Lexer and Parser helper functions.                                 -/
/- ------------------------------------------------------------------------- -/
-/

abbrev token := String
abbrev tokens := List token
abbrev parser (a : Type) := tokens -> a × tokens

def matches_ (parent_str : String) (char : Char) : Bool :=
  let chars: List Char := parent_str.toList
  List.elem char chars

def space := matches_ " \t\r\n"
def punctuation := matches_ "(){}[],"
def symbolic := matches_ "~`!@#$%^&*-+:=|\\:;<>.?/"
def numeric := matches_ "0123456789"
def alphanumeric :=
  matches_ "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

def implode : List Char -> String := fun inp => String.join (List.map Char.toString inp)

def lexwhile (prop : Char -> Bool) (inp: List Char) : token × List Char :=
  match inp with
  | [] => ("", inp)
  | c :: cs =>
    if prop c then
      let (tok, rest) := lexwhile prop cs
      (String.append c.toString tok, rest)
    else ("", inp)
termination_by lexwhile prop inp => List.length inp

/- lexer -/
def lex (inp : List Char) : tokens :=
  match (lexwhile space inp).snd with
  | [] => []
  | c :: cs =>
      let prop :=
        if alphanumeric c then alphanumeric
        else if symbolic c then symbolic
        else fun _ => false /- for punctuation we stop at one char -/

      let (tok, rest) := lexwhile prop cs
      (String.append c.toString tok) :: lex rest
termination_by lex inp => List.length inp
decreasing_by
  simp_wf
  sorry


/- Wrap a parser function along with the lexer -/
def make_parser {α : Type} [Inhabited α] (pfn: parser α) (inp: String) : α :=
  let toks := lex inp.toList
  match pfn toks with
  | (e, []) => e
  | _ => panic! "unexpected trailing input"


/-
Examples
-/

#eval lex (String.toList "2*((var_1 + x') + 11)") == ["2", "*", "(", "(", "var_1", "+", "x'", ")", "+", "11", ")"]

example : lex (String.toList "2*((var_1 + x') + 11)") =
  ["2", "*", "(", "(", "var_1", "+", "x'", ")", "+", "11", ")"] := by rfl

example : lex (String.toList "if (*p1-- == *p2++) then f() else g()")
  = [
      "if",
      "(",
      "*",
      "p1",
      "--",
      "==",
      "*",
      "p2",
      "++",
      ")",
      "then",
      "f",
      "(",
      ")",
      "else",
      "g",
      "(",
      ")"
    ] := by rfl