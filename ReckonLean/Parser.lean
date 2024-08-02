import ReckonLean.Common

/- ------------------------------------------------------------------------- -/
/- Lexer helper functions.                                                   -/
/- ------------------------------------------------------------------------- -/

abbrev token := String
abbrev tokens := List token

def matches_ (parent_str : String) (char : Char) : Bool :=
  let chars: List Char := parent_str.toList
  List.elem char chars

def space := matches_ " \t\r\n"
def punctuation := matches_ "(){}[],"
def symbolic := matches_ "~`!@#$%^&*-+:=|\\:;<>.?/∧∨"
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
termination_by inp.length

/- The `Char`s argument of `lexwhile` monotonically decreases -/
theorem lexwhile_monotonic : ∀ (p : Char → Bool) (inp: List Char), (lexwhile p inp).snd.length ≤ inp.length := by
  intro p inp
  induction inp with
  | nil => simp [lexwhile]
  | cons c cs ih =>
    simp [lexwhile]
    cases p c <;> simp
    exact Nat.le_succ_of_le ih

/- lexer -/
def lex (inp : List Char) : tokens :=
  match _hlw : (lexwhile space inp).snd with
  | [] => []
  | c :: cs =>
      let prop :=
        if alphanumeric c then alphanumeric
        else if symbolic c then symbolic
        else fun _ => false /- for punctuation we stop at one char -/

      let trest := lexwhile prop cs
      (String.append c.toString trest.fst) :: lex trest.snd
termination_by inp.length
decreasing_by
  simp_wf
  calc
    (lexwhile prop cs).snd.length ≤ cs.length := lexwhile_monotonic prop cs
    _ < Nat.succ (cs).length := Nat.lt_of_succ_le (Nat.le_refl _)
    _ = (c :: cs).length := List.length_cons c cs
    _ = (lexwhile space inp).snd.length := by rw [_hlw]
    _ ≤ inp.length := lexwhile_monotonic space inp


/- ------------------------------------------------------------------------- -/
/- Parser helper functions.                                                  -/
/- ------------------------------------------------------------------------- -/

/--
Parser type. The usual convention applies here:

* empty list corresponds to a parse error
* a non-empty list corresponds to distinct parse results
* if the grammar is not ambiguous, the list is singleton
-/
structure ParseResult (a : Type) where
  res: List a

def ParseResult.error : ParseResult a := ParseResult.mk []

instance : Coe (List α) (ParseResult α) where
  coe := ParseResult.mk

-- This is not ideal since Lean is has a strict evaluation strategy, but it's fine
-- for our purposes. The formulas given to the parser are all small and hand written. Larger
-- formulas are generated from the AST directly.
--
-- TODO: use Std.Data.MLList.Basic in place of List
instance : Monad ParseResult where
  pure := ParseResult.mk ∘ List.pure
  bind x f := ParseResult.mk (List.bind x.res (ParseResult.res ∘ f))

instance : HAppend (ParseResult a) (ParseResult a) (ParseResult a) where
  hAppend r1 r2 := ⟨ r1.res ++ r2.res ⟩

abbrev parser (a : Type) := tokens -> ParseResult (a × tokens)

/- Wrap a parser function along with the lexer -/
def make_parser {α : Type} [Inhabited α] (pfn: parser α) (inp: String) : Option α :=
  let toks := lex inp.toList
  match pfn toks with
  | ⟨ [] ⟩ =>
    -- uncomment for parser debugging
    -- dbg_trace "parser error"
    none
  | ⟨ [(e, [])] ⟩ => some e
  | _ =>
    dbg_trace "unexpected trailing input"; none


/- ------------------------------------------------------------------------- -/
/- Examples                                                                  -/
/- ------------------------------------------------------------------------- -/

#guard lex (String.toList "2*((var_1 + x') + 11)") == ["2", "*", "(", "(", "var_1", "+", "x'", ")", "+", "11", ")"]
#guard lex (String.toList "p ∧ q") == ["p", "∧", "q"]

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
