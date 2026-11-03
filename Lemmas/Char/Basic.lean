module

public import Init.Meta

import all ParseIt.Error
import all ParseIt.Basic
import ParseIt.Combinators
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
/-- If every step `f c` either yields while consuming input or fails with an `unexpected` error,
then `forIn l` over `f` consumes input whenever `l` is non-empty, and any failure is an
`unexpected` error. -/
theorem string_loop (l : List Char) (f : Char → PUnit → Parser ε ι Char (ForInStep PUnit))
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
theorem string_eq (tk : String) :
    (ParseIt.Char.string tk : Parser ε ι Char String) =
    withErrorMessage s!"expected {repr tk}"
      ((forIn tk.toList PUnit.unit (fun c (_ : PUnit) => do discard (token c); pure (ForInStep.yield PUnit.unit)) : Parser ε ι Char PUnit) >>= fun _ => pure tk) := by
  unfold ParseIt.Char.string
  rw [String.forIn_eq_forIn_toList]

omit [Iterators.Finite ι Id] in
/-- Evaluation of `string tk` at `it` in terms of the character loop. -/
theorem string_eq_apply (tk : String) (it : Iter (α := ι) Char) :
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
theorem body_ok (c : Char) (it : Iter (α := ι) Char) :
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
