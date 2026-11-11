module

public import Init.Meta

import all ParseIt.Error
import all ParseIt.Basic
import all ParseIt.Char.Basic

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax
public import Std.WP

public import Lemmas.Instances
public import Lemmas.Basic
public import Lemmas.Combinators

open Std Std.WP Lean ParseIt ParseIt.Char

@[expose] public section

set_option experimental.vcgen true

namespace ParseIt.Char

/-! Theorems for ParseIt.Char.Basic -/

variable {ε ι : Type} [Iterator ι Id Char] [Iterators.Productive ι Id] [Iterators.Finite ι Id] [Error ε ι Char]

/-- `char c` succeeds with `c` when the next character is `c`, consuming input; otherwise it fails
with an `unexpected` error annotated with `expected c`. -/
@[spec] theorem Spec.char (c : Char)
  (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.char c : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = c
                ∧ (ParseIt.Char.char c : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t, e = ((Error.addMessage (Error.unexpected it t)) it s!"expected {repr c}")) := by
  have h := Spec.withErrorMessage (token c : Parser ε ι Char Char) (Spec.token c it) s!"expected {repr c}" it
  vcgen [ParseIt.Char.char, h] with try finish
  simp [Char.char]
  grind

omit [Iterators.Productive ι Id] in
omit [Iterators.Finite ι Id] in
/-- If every step `f c` either yields while consuming input or fails with an `unexpected` error,
then `forIn l` over `f` consumes input whenever `l` is non-empty, and any failure is an
`unexpected` error. -/
private theorem string_loop (l : List Char) (f : Char → PUnit → Parser ε ι Char (ForInStep PUnit))
  (hf : ∀ c it, match f c PUnit.unit it with
    | .ok rest _ y => y = .yield PUnit.unit ∧ Advanced rest it
    | .error e => ∃ (it' : Iter (α := ι) Char) (t : Option Char), e = Error.unexpected it' t)
  (it : Iter (α := ι) Char) :
    match (forIn l PUnit.unit f : Parser ε ι Char PUnit) it with
    | .ok rest _ _ => l ≠ [] → Advanced rest it
    | .error e => ∃ (it' : Iter (α := ι) Char) (t : Option Char), e = Error.unexpected it' t := by
  induction l generalizing it with
  | nil => simp [pure]
  | cons c l ih =>
    simp only [List.forIn_cons, bind]
    have hc := hf c it
    revert hc
    cases f c PUnit.unit it with
    | error e => exact id
    | ok rest h y =>
      rintro ⟨rfl, hadv⟩
      simp only [pure]
      have := ih rest
      revert this
      generalize forIn l PUnit.unit f rest = r
      cases r with
      | error e => exact id
      | ok rest' h' _ =>
        intro _ _
        exact Progress.advanced_of_trans h' hadv

omit [Iterators.Finite ι Id] in
/-- `string tk` unfolded: match each character of `tk` with `token`, return `tk`, and annotate
errors with `expected tk`. -/
private theorem string_eq (tk : String) :
    (ParseIt.Char.string tk : Parser ε ι Char String) =
    withErrorMessage s!"expected {repr tk}"
      ((forIn tk.toList PUnit.unit (fun c (_ : PUnit) => do discard (token c); pure (ForInStep.yield PUnit.unit)) : Parser ε ι Char PUnit) >>= fun _ => pure tk) := by
  unfold ParseIt.Char.string
  rw [String.forIn_eq_forIn_toList]

omit [Iterators.Finite ι Id] in
/-- Evaluation of `string tk` at `it` in terms of the character loop. -/
private theorem string_eq_apply (tk : String) (it : Iter (α := ι) Char) :
    (ParseIt.Char.string tk : Parser ε ι Char String) it =
    match (forIn tk.toList PUnit.unit (fun c (_ : PUnit) => do discard (token c); pure (ForInStep.yield PUnit.unit)) : Parser ε ι Char PUnit) it with
    | .ok rest h _ => .ok rest h tk
    | .error e => .error (Error.addMessage e it s!"expected {repr tk}") := by
  rw [string_eq]
  generalize (forIn tk.toList PUnit.unit _ : Parser ε ι Char PUnit) = x
  simp only [withErrorMessage, bind, pure]
  cases x it <;> simp

omit [Iterators.Finite ι Id] in
/-- The loop body of `string` (match a single character `c`) yields while consuming input, or fails
with an `unexpected` error. -/
private theorem body_ok (c : Char) (it : Iter (α := ι) Char) :
    match ((do discard (token c); pure (ForInStep.yield PUnit.unit)) : Parser ε ι Char (ForInStep PUnit)) it with
    | .ok rest _ y => y = .yield PUnit.unit ∧ Advanced rest it
    | .error e => ∃ (it' : Iter (α := ι) Char) (t : Option Char), e = Error.unexpected it' t := by
  have ht := Parser.of_wp_eq _ (Spec.token (ε := ε) c it) it (by simp [IterWithProgress.refl])
  simp only [discard, Functor.mapConst, bind, pure, Function.comp, Function.const]
  revert ht
  cases (token c : Parser ε ι Char Char) it with
  | ok => simp
  | error => simp only []; grind

/-- `string tk` succeeds with `tk` when the input starts with `tk`, consuming input if `tk` is
non-empty; otherwise it fails with an `unexpected` error annotated with `expected tk`. -/
@[spec] theorem Spec.string (tk : String)
  (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.string tk : Parser ε ι Char String)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = tk
                ∧ (ParseIt.Char.string t : Parser ε ι Char String) s.it = .ok s.rest s.p t
                ∧ (tk ≠ "" → Advanced s.rest s.it))
        (fun e => ∃ (it' : Iter (α := ι) Char) (t : Option Char),
          e = ((Error.addMessage (Error.unexpected it' t)) it s!"expected {repr tk}")) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, wp, WP.trans, Parser.run, pushResult]
    rintro ⟨it₀, rest, p⟩ ⟨h₁, h₂⟩
    dsimp only at h₁ h₂ ⊢
    subst it₀ rest
    rw [Progress.eq_refl p]
    have hl := string_loop tk.toList
      (fun c (_ : PUnit) => (do discard (token c); pure (ForInStep.yield PUnit.unit) : Parser ε ι Char _))
      (fun c it => body_ok c it) it
    rw [string_eq_apply]
    revert hl
    generalize hr : (forIn tk.toList PUnit.unit _ : Parser ε ι Char PUnit) it = r
    cases r with
    | ok rest h _ =>
      intro hl
      exact ⟨rfl, rfl, by rw [string_eq_apply, hr]; simp, fun hne => hl (by simpa using hne)⟩
    | error e =>
      rintro ⟨it', t, rfl⟩
      exact ⟨it', t, rfl⟩)

/-- `space` succeeds with `' '` when the next character is a space (U+0020), consuming input;
otherwise it fails with an `unexpected` error annotated with `expected space (U+0020)`. -/
@[spec] theorem Spec.space (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.space : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = ' '
                ∧ (ParseIt.Char.space : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t, e = ((Error.addMessage (Error.unexpected it t)) it "expected space (U+0020)")) := by
  have h := Spec.withErrorMessage (token ' ' : Parser ε ι Char Char) (Spec.token ' ' it)
    "expected space (U+0020)" it
  vcgen [ParseIt.Char.space, h] with try finish
  simp [Char.space]
  grind

/-- `tab` succeeds with `'\t'` when the next character is a horizontal tab (U+0009), consuming input;
otherwise it fails with an `unexpected` error annotated with `expected horizontal tab (U+0009)`. -/
@[spec] theorem Spec.tab (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.tab : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = '\t'
                ∧ (ParseIt.Char.tab : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected horizontal tab (U+0009)")) := by
  have h := Spec.withErrorMessage (token '\t' : Parser ε ι Char Char) (Spec.token '\t' it)
    "expected horizontal tab (U+0009)" it
  vcgen [ParseIt.Char.tab, h] with try finish
  simp [Char.tab]
  grind

/-- `ASCII.lf` succeeds with `'\n'` when the next character is a line feed (U+000A), consuming
input; otherwise it fails with an `unexpected` error annotated with `expected line feed (U+000A)`. -/
@[spec] theorem Spec.ASCII.lf (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.lf : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = '\n'
                ∧ (ParseIt.Char.ASCII.lf : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected line feed (U+000A)")) := by
  have h := Spec.withErrorMessage (token '\n' : Parser ε ι Char Char) (Spec.token '\n' it)
    "expected line feed (U+000A)" it
  vcgen [ParseIt.Char.ASCII.lf, h] with try finish
  simp [Char.ASCII.lf]
  grind

/-- `ASCII.cr` succeeds with `'\r'` when the next character is a carriage return (U+000D),
consuming input; otherwise it fails with an `unexpected` error annotated with
`expected carriage return (U+000D)`. -/
@[spec] theorem Spec.ASCII.cr (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.cr : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = '\r'
                ∧ (ParseIt.Char.ASCII.cr : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected carriage return (U+000D)")) := by
  have h := Spec.withErrorMessage (token '\r' : Parser ε ι Char Char) (Spec.token '\r' it)
    "expected carriage return (U+000D)" it
  vcgen [ParseIt.Char.ASCII.cr, h] with try finish
  simp [Char.ASCII.cr]
  grind

omit [Iterators.Finite ι Id] in
/-- Evaluation of `eol` at `it`: try `cr *> lf`, then `lf` from the same position; if both fail,
merge their errors and annotate the result with `expected newline`. -/
private theorem eol_apply (it : Iter (α := ι) Char) :
    (ParseIt.Char.eol : Parser ε ι Char Char) it =
      match (ParseIt.Char.ASCII.cr *> ParseIt.Char.ASCII.lf : Parser ε ι Char Char) it with
      | .ok rest h x => .ok rest h x
      | .error e₁ =>
        match (ParseIt.Char.ASCII.lf : Parser ε ι Char Char) it with
        | .ok rest h x => .ok rest h x
        | .error e₂ => .error (Error.addMessage (Error.merge (ι := ι) e₁ e₂) it "expected newline") := by
  simp only [ParseIt.Char.eol, withErrorMessage, HOrElse.hOrElse, OrElse.orElse, bind, pure]
  cases (ParseIt.Char.ASCII.cr *> ParseIt.Char.ASCII.lf : Parser ε ι Char Char) it <;>
    cases (ParseIt.Char.ASCII.lf : Parser ε ι Char Char) it <;> rfl

/-- `eol` at `it` either succeeds with `'\n'`, consuming input, or fails with the error `e₁` of
`cr *> lf` (a failed `cr` at `it` or a failed `lf` after it) merged with the error of `lf` at `it`,
annotated with `expected newline`. -/
private theorem eol_of_eq (it : Iter (α := ι) Char) {r}
  (h : (ParseIt.Char.eol : Parser ε ι Char Char) it = r)
    : (∃ (rest : Iter (α := ι) Char) (p : Progress rest it), Advanced rest it ∧ r = .ok rest p '\n')
      ∨ (∃ (e₁ : ε) (t : Option Char),
          ((∃ t', e₁ = Error.addMessage (Error.unexpected it t') it "expected carriage return (U+000D)")
            ∨ ∃ (it' : Iter (α := ι) Char) (t' : Option Char),
              e₁ = Error.addMessage (Error.unexpected it' t') it' "expected line feed (U+000A)")
          ∧ r = .error (Error.addMessage (Error.merge (ι := ι) e₁
              (Error.addMessage (Error.unexpected it t) it "expected line feed (U+000A)"))
              it "expected newline")) := by
  subst h
  rw [eol_apply]
  have hcr := Parser.of_wp_eq _ (Spec.ASCII.cr (ε := ε) it) it (by simp [IterWithProgress.refl])
  have hlf := Parser.of_wp_eq _ (Spec.ASCII.lf (ε := ε) it) it (by simp [IterWithProgress.refl])
  simp only [SeqRight.seqRight, bind, pure]
  revert hcr
  cases (ParseIt.Char.ASCII.cr : Parser ε ι Char Char) it with
  | ok r₁ p₁ c =>
    rintro ⟨-, -, -, ha₁⟩
    dsimp only
    have hlf' := Parser.of_wp_eq _ (Spec.ASCII.lf (ε := ε) r₁) r₁ (by simp [IterWithProgress.refl])
    revert hlf'
    cases (ParseIt.Char.ASCII.lf : Parser ε ι Char Char) r₁ with
    | ok r₂ p₂ c₂ =>
      rintro ⟨-, rfl, -, ha₂⟩
      exact .inl ⟨r₂, _, Progress.advanced_of_trans p₂ ha₁, rfl⟩
    | error e₁ =>
      rintro ⟨t', rfl⟩
      revert hlf
      cases (ParseIt.Char.ASCII.lf : Parser ε ι Char Char) it with
      | ok r₂ p₂ c₂ =>
        rintro ⟨-, rfl, -, ha₂⟩
        exact .inl ⟨r₂, p₂, ha₂, rfl⟩
      | error e₂ =>
        rintro ⟨t, rfl⟩
        exact .inr ⟨_, t, .inr ⟨r₁, t', rfl⟩, rfl⟩
  | error e₁ =>
    rintro ⟨t', rfl⟩
    revert hlf
    cases (ParseIt.Char.ASCII.lf : Parser ε ι Char Char) it with
    | ok r₂ p₂ c₂ =>
      rintro ⟨-, rfl, -, ha₂⟩
      exact .inl ⟨r₂, p₂, ha₂, rfl⟩
    | error e₂ =>
      rintro ⟨t, rfl⟩
      exact .inr ⟨_, t, .inl ⟨t', rfl⟩, rfl⟩

/-- `eol` succeeds with `'\n'` on a line feed, optionally preceded by a carriage return, consuming
input. Otherwise it fails with the error `e₁` of `cr *> lf` (a failed `cr` at `it`, or a failed
`lf` after a `cr`) merged with the error of `lf` at `it`, annotated with `expected newline`. -/
@[spec] theorem Spec.eol (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.eol : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = '\n'
                ∧ (ParseIt.Char.eol : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ (e₁ : ε) (t : Option Char),
          ((∃ t', e₁ = Error.addMessage (Error.unexpected it t') it "expected carriage return (U+000D)")
            ∨ ∃ (it' : Iter (α := ι) Char) (t' : Option Char),
              e₁ = Error.addMessage (Error.unexpected it' t') it' "expected line feed (U+000A)")
          ∧ e = Error.addMessage (Error.merge (ι := ι) e₁
              (Error.addMessage (Error.unexpected it t) it "expected line feed (U+000A)"))
              it "expected newline") :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro ⟨sit, srest, sp⟩ ⟨hit, hrest⟩
    dsimp only at hit hrest ⊢
    subst hit hrest
    rw [Progress.eq_refl sp]
    generalize hr : (ParseIt.Char.eol : Parser ε ι Char Char) srest = r
    rcases eol_of_eq srest hr with ⟨rest, p, ha, rfl⟩ | ⟨e₁, t, he₁, rfl⟩
    · rw [pushResult_ok]
      exact ⟨rfl, rfl, by simp, by simpa using ha⟩
    · exact ⟨e₁, t, he₁, rfl⟩)

/-- `ASCII.whitespace` succeeds with a whitespace character `t` (space or U+0009 to U+000D), consuming input; otherwise it fails with an
`unexpected` error annotated with `expected whitespace character`. -/
@[spec] theorem Spec.ASCII.whitespace (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.whitespace : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ (t = ' ' ∨ ('\t' ≤ t ∧ t ≤ '\r'))
                ∧ (ParseIt.Char.ASCII.whitespace : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected whitespace character")) := by
  have h := Spec.withErrorMessage
    (tokenFilter (fun c => c == ' ' || c >= '\t' && c <= '\r') : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected whitespace character" it
  vcgen [ParseIt.Char.ASCII.whitespace, h] with try finish
  simp [Char.ASCII.whitespace]
  grind

/-- `ASCII.uppercase` succeeds with an uppercase letter `t` (`A` to `Z`), consuming input;
otherwise it fails with an `unexpected` error annotated with
`expected uppercase letter character`. -/
@[spec] theorem Spec.ASCII.uppercase (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.uppercase : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ 'A' ≤ t ∧ t ≤ 'Z'
                ∧ (ParseIt.Char.ASCII.uppercase : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected uppercase letter character")) := by
  have h := Spec.withErrorMessage (tokenFilter (fun c => c >= 'A' && c <= 'Z') : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected uppercase letter character" it
  vcgen [ParseIt.Char.ASCII.uppercase, h] with try finish
  simp [Char.ASCII.uppercase]
  grind

/-- `ASCII.lowercase` succeeds with a lowercase letter `t` (`a` to `z`), consuming input; otherwise it fails with an
`unexpected` error annotated with `expected lowercase letter character`. -/
@[spec] theorem Spec.ASCII.lowercase (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.lowercase : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ 'a' ≤ t ∧ t ≤ 'z'
                ∧ (ParseIt.Char.ASCII.lowercase : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected lowercase letter character")) := by
  have h := Spec.withErrorMessage
    (tokenFilter (fun c => c >= 'a' && c <= 'z') : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected lowercase letter character" it
  vcgen [ParseIt.Char.ASCII.lowercase, h] with try finish
  simp [Char.ASCII.lowercase]
  grind

/-- `ASCII.alpha` succeeds with an alphabetic character `t` (`A` to `Z` or `a` to `z`), consuming input; otherwise it fails with an
`unexpected` error annotated with `expected alphabetic character`. -/
@[spec] theorem Spec.ASCII.alpha (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.alpha : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ (('A' ≤ t ∧ t ≤ 'Z') ∨ ('a' ≤ t ∧ t ≤ 'z'))
                ∧ (ParseIt.Char.ASCII.alpha : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected alphabetic character")) := by
  have h := Spec.withErrorMessage
    (tokenFilter (fun c => if c >= 'a' then c <= 'z' else c >= 'A' && c <= 'Z') : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected alphabetic character" it
  vcgen [ParseIt.Char.ASCII.alpha, h] with try finish
  simp [Char.ASCII.alpha]
  grind

/-- `ASCII.numeric` succeeds with a decimal digit character `t` (`0` to `9`), consuming input; otherwise it fails with an
`unexpected` error annotated with `expected decimal digit character`. -/
@[spec] theorem Spec.ASCII.numeric (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.numeric : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ '0' ≤ t ∧ t ≤ '9'
                ∧ (ParseIt.Char.ASCII.numeric : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected decimal digit character")) := by
  have h := Spec.withErrorMessage
    (tokenFilter (fun c => c >= '0' && c <= '9') : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected decimal digit character" it
  vcgen [ParseIt.Char.ASCII.numeric, h] with try finish
  simp [Char.ASCII.numeric]
  grind

/-- `ASCII.alphanum` succeeds with a letter or digit character `t` (`A` to `Z`, `a` to `z` or `0` to `9`), consuming input; otherwise it fails with an
`unexpected` error annotated with `expected letter or digit character`. -/
@[spec] theorem Spec.ASCII.alphanum (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.alphanum : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ (('A' ≤ t ∧ t ≤ 'Z') ∨ ('a' ≤ t ∧ t ≤ 'z') ∨ ('0' ≤ t ∧ t ≤ '9'))
                ∧ (ParseIt.Char.ASCII.alphanum : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected letter or digit character")) := by
  have h := Spec.withErrorMessage
    (tokenFilter (fun c => if c >= 'a' then c <= 'z' else if c >= 'A' then c <= 'Z' else c >= '0' && c <= '9') : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected letter or digit character" it
  vcgen [ParseIt.Char.ASCII.alphanum, h] with try finish
  simp [Char.ASCII.alphanum]
  grind

/-- `ASCII.control` succeeds with a control character `t` (U+0000 to U+001F or U+007F), consuming input; otherwise it fails with an
`unexpected` error annotated with `expected control character`. -/
@[spec] theorem Spec.ASCII.control (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.control : Parser ε ι Char Char)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ (t.val < 0x20 ∨ t.val = 0x7f)
                ∧ (ParseIt.Char.ASCII.control : Parser ε ι Char Char) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected control character")) := by
  have h := Spec.withErrorMessage
    (tokenFilter (fun c => c.val < 0x20 || c.val == 0x7f) : Parser ε ι Char Char)
    (Spec.tokenFilter _ it) "expected control character" it
  vcgen [ParseIt.Char.ASCII.control, h] with try finish
  simp [Char.ASCII.control]
  grind

/-- `withErrorMessage msg (tokenMap f)` reads one character `t` and succeeds with `a` when
`f t = some a`, consuming input; otherwise it fails with an `unexpected` error annotated with
`msg`. -/
@[spec] theorem Spec.withErrorMessage_tokenMap {α : Type} (f : Char → Option α) (msg : String)
  (it : Iter (α := ι) Char)
    : Triple (withErrorMessage msg (tokenMap f) : Parser ε ι Char α)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (∃ t, f t = some a)
                ∧ (withErrorMessage msg (tokenMap f) : Parser ε ι Char α) s.it = .ok s.rest s.p a
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t, e = ((Error.addMessage (Error.unexpected it t)) it msg)) := by
  have h := Spec.withErrorMessage (tokenMap f : Parser ε ι Char α) (Spec.tokenMap f it) msg it
  vcgen [h] with try finish
  all_goals grind

/-- `ASCII.digit` succeeds with the value of a decimal digit (`0` to `9`), consuming input; otherwise it
fails with an `unexpected` error annotated with `expected decimal digit`. -/
@[spec] theorem Spec.ASCII.digit (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.digit : Parser ε ι Char (Fin 10))
        (fun s => s.it = it ∧ s.rest = it)
        (fun d s => s.it = it
                ∧ (ParseIt.Char.ASCII.digit : Parser ε ι Char (Fin 10)) s.it = .ok s.rest s.p d
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected decimal digit")) :=
  Triple.intro (Triple.entails_wp_of_post (Spec.withErrorMessage_tokenMap _ _ it)
    (fun _ _ h => ⟨h.1, h.2.2⟩))

/-- `ASCII.binDigit` succeeds with the value of a binary digit (`0` or `1`), consuming input; otherwise it
fails with an `unexpected` error annotated with `expected binary digit`. -/
@[spec] theorem Spec.ASCII.binDigit (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.binDigit : Parser ε ι Char (Fin 2))
        (fun s => s.it = it ∧ s.rest = it)
        (fun d s => s.it = it
                ∧ (ParseIt.Char.ASCII.binDigit : Parser ε ι Char (Fin 2)) s.it = .ok s.rest s.p d
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected binary digit")) :=
  Triple.intro (Triple.entails_wp_of_post (Spec.withErrorMessage_tokenMap _ _ it)
    (fun _ _ h => ⟨h.1, h.2.2⟩))

/-- `ASCII.octDigit` succeeds with the value of an octal digit (`0` to `7`), consuming input; otherwise it
fails with an `unexpected` error annotated with `expected octal digit`. -/
@[spec] theorem Spec.ASCII.octDigit (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.octDigit : Parser ε ι Char (Fin 8))
        (fun s => s.it = it ∧ s.rest = it)
        (fun d s => s.it = it
                ∧ (ParseIt.Char.ASCII.octDigit : Parser ε ι Char (Fin 8)) s.it = .ok s.rest s.p d
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected octal digit")) :=
  Triple.intro (Triple.entails_wp_of_post (Spec.withErrorMessage_tokenMap _ _ it)
    (fun _ _ h => ⟨h.1, h.2.2⟩))

/-- `ASCII.hexDigit` succeeds with the value of a hexadecimal digit (`0` to `9`, `A` to `F` or `a` to `f`), consuming input; otherwise it
fails with an `unexpected` error annotated with `expected hexadecimal digit`. -/
@[spec] theorem Spec.ASCII.hexDigit (it : Iter (α := ι) Char)
    : Triple (ParseIt.Char.ASCII.hexDigit : Parser ε ι Char (Fin 16))
        (fun s => s.it = it ∧ s.rest = it)
        (fun d s => s.it = it
                ∧ (ParseIt.Char.ASCII.hexDigit : Parser ε ι Char (Fin 16)) s.it = .ok s.rest s.p d
                ∧ Advanced s.rest s.it)
        (fun e => ∃ t,
          e = ((Error.addMessage (Error.unexpected it t)) it "expected hexadecimal digit")) :=
  Triple.intro (Triple.entails_wp_of_post (Spec.withErrorMessage_tokenMap _ _ it)
    (fun _ _ h => ⟨h.1, h.2.2⟩))
