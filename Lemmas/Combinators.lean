module

public import Init.Meta

import all ParseIt.Basic
import all ParseIt.Combinators

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax
public import Std.WP

public import Lemmas.Instances
public import Lemmas.Basic

open Std Std.WP Lean ParseIt ParseIt.Char

@[expose] public section

set_option experimental.vcgen true

namespace ParseIt

/-! Theorems for ParseIt.Combinators -/

variable {ε ι τ α : Type u} [Iterator ι Id τ]

/-- Any result `b` of `nextToken it yield done` comes either from `yield` applied to an iterator that
has advanced past `it` and the token read, or from `done` (end of input). -/
theorem nextToken_of_eq [Iterators.Productive ι Id] {β : Sort _} (it : Iter (α := ι) τ)
  (yield : (rest : Iter (α := ι) τ) → Advanced rest it → τ → β) (done : Unit → β) (b)
  (h : nextToken it yield done = b)
    : (∃ (it' : Iter (α := ι) τ) (h : Advanced it' it) (x : τ), yield it' h x = b)
      ∨ done () = b  := by
  fun_induction nextToken <;> grind

/-- `tokenMap f` reads one token `t` and succeeds with `a` when `f t = some a`, consuming input.
It fails with `Error.unexpected it none` at end of input, or with `Error.unexpected it (some t)`
when `f t = none`. -/
@[spec] theorem Spec.tokenMap [Iterators.Productive ι Id] [Error ε ι τ]
  (f : τ → Option α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.tokenMap f : Parser ε ι τ α)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (∃ t, f t = some a)
                ∧ (ParseIt.tokenMap f : Parser ε ι τ α) s.it = .ok s.rest s.p a
                ∧ Advanced s.rest s.it)
        (fun e => e = (Error.unexpected it none) ∨ ∃ (t : τ), f t = none ∧ e = (Error.unexpected it (some t))) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl⟩
    generalize hr : (ParseIt.tokenMap f : Parser ε ι τ α) s.rest = r
    have hr' := hr
    simp only [ParseIt.tokenMap, pure] at hr'
    rcases nextToken_of_eq _ _ _ _ hr' with ⟨it', h, x, hx⟩ | hx
    · split at hx <;> subst hx
      · obtain ⟨_, _, p⟩ := s
        dsimp only at hit h hr ⊢
        subst hit
        cases p <;> exact ⟨rfl, ⟨_, ‹_›⟩, hr, h⟩
      · grind
    · subst hx
      grind)

/-- `anyToken` reads and returns one token, consuming input; it fails with an `unexpected` error
at `it`. -/
@[spec] theorem Spec.anyToken [Iterators.Productive ι Id] [Error ε ι τ]
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.anyToken : Parser ε ι τ τ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it
                ∧ (ParseIt.anyToken : Parser ε ι τ τ) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => e = (Error.unexpected it none) ∨ ∃ (t : τ), e = (Error.unexpected it (some t))) := by
  vcgen [ParseIt.anyToken] with try finish
  simp only [ParseIt.anyToken]
  grind

/-- `tokenFilter test` reads one token `t` and succeeds when `test t` holds, consuming input. It
fails at end of input or with `Error.unexpected it (some t)` when `test t` is false. -/
@[spec] theorem Spec.tokenFilter [Iterators.Productive ι Id] [Error ε ι τ]  (test : τ → Bool)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.tokenFilter test : Parser ε ι τ τ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ test t = True
                ∧ (ParseIt.tokenFilter test : Parser ε ι τ τ) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => e = (Error.unexpected it none) ∨ ∃ (t : τ), test t = False ∧ e = (Error.unexpected it (some t))) := by
  vcgen [ParseIt.tokenFilter] with try finish
  simp only [ParseIt.tokenFilter]
  grind

/-- `token tk` succeeds with `tk` when the next token equals `tk`, consuming input. It fails at end
of input or with `Error.unexpected it (some t)` when the next token `t` differs from `tk`. -/
@[spec] theorem Spec.token [Iterators.Productive ι Id] [Error ε ι τ] [BEq τ] [LawfulBEq τ] (tk : τ)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.token tk : Parser ε ι τ τ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun t s => s.it = it ∧ t = tk
                ∧ (ParseIt.token tk : Parser ε ι τ τ) s.it = .ok s.rest s.p t
                ∧ Advanced s.rest s.it)
        (fun e => e = (Error.unexpected it none) ∨ ∃ (t : τ), t != tk ∧ e = (Error.unexpected it (some t))) := by
  vcgen [ParseIt.token] with try finish
  simp only [ParseIt.token]
  grind

/-- `endOfInput` succeeds without consuming input; any failure is an `unexpected` error at `it`. -/
@[spec] theorem Spec.endOfInput [Iterators.Productive ι Id] [Error ε ι τ]
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.endOfInput : Parser ε ι τ Unitᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun _ s => s.it = it ∧ s.rest = it)
        (fun e => e = (Error.unexpected it none) ∨ ∃ (t : τ), e = (Error.unexpected it (some t))) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run, ParseIt.endOfInput,
                pushResult, pure]
    rintro s ⟨hit, rfl⟩
    generalize hr : nextToken s.rest _ _ = r
    rcases nextToken_of_eq _ _ _ _ hr with ⟨_, _, _, hx⟩ | hx <;> subst hx
    · grind only
    · exact ⟨hit, rfl⟩)

/-- efoldlP.loop always returns .ok -/
theorem efoldlP.loop_eq_ok  [Iterators.Finite ι Id]
  (f : β → α → ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) it y cur (hcur : Progress cur it)
    : ∃ rest h x, ParseIt.efoldlP.loop f p it y cur hcur = .ok rest h x := by
  fun_induction efoldlP.loop f p it y cur hcur
  simp [bind, pure]
  repeat split <;> try grind
  simp_all

/-- efoldlP always returns .ok -/
theorem efoldlP_eq_ok  [Iterators.Finite ι Id]
  (f : β → α → ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) it y
    : ∃ rest h x, ParseIt.efoldlP f y p it = .ok rest h x := by
  have := efoldlP.loop_eq_ok f p it y it (.refl it)
  simp_all [ParseIt.efoldlP]

/-- every element collected by the fold loop satisfies `P` if every successful `p` result does -/
theorem efoldlP.loop_all [Iterators.Finite ι Id] (P : α → Prop) (it cur) (hcur : Progress cur it)
  (y : Array α) (p : ParserT ε ι τ Id α)
  (hp : ∀ s rest h x, Progress s it → p s = .ok rest h x → P x)
  (hy : ∀ a ∈ y, P a) {rest h' z}
  (heq : efoldlP.loop (fun y x => pure (y.push x)) p it y cur hcur = .ok rest h' z)
    : ∀ a ∈ z.1, P a := by
  fun_induction efoldlP.loop (fun y x => pure (y.push x)) p it y cur hcur
  rename_i s y cur hcur ih
  simp only [bind, pure] at heq
  split at heq
  · cases heq; exact hy
  · rename_i hpx
    split at heq
    · cases heq
      simp only [Array.mem_push]
      rintro a (ha | rfl)
      · exact hy a ha
      · exact hp _ _ _ _ hcur hpx
    · rename_i x _ _ _
      refine ih _ (y.push x) _ ?_ heq
      simp only [Array.mem_push]
      rintro a (ha | rfl)
      · exact hy a ha
      · exact hp _ _ _ _ hcur hpx

/-- If `p` always consumes input on success, then the push fold loop never reports an error
(`z.2 = none`), remains advanced once `cur` has advanced past `it`, and has advanced past `it`
whenever the accumulator changed. -/
theorem efoldlP.loop_push_advanced [Iterators.Finite ι Id] (it cur) (hcur : Progress cur it)
  (y : Array α) (p : ParserT ε ι τ Id α)
  (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s) {rest h' z}
  (heq : efoldlP.loop (fun y x => pure (y.push x)) p it y cur hcur = .ok rest h' z)
    : z.2 = none ∧ (Advanced cur it → Advanced rest it) ∧ (z.1 ≠ y → Advanced rest it) := by
  fun_induction efoldlP.loop (fun y x => pure (y.push x)) p it y cur hcur
  rename_i s y cur hcur ih
  simp only [bind, pure] at heq
  split at heq
  · cases heq; exact ⟨rfl, id, fun h => absurd rfl h⟩
  · rename_i hpx
    split at heq
    · cases heq
      subst ‹rest = cur›
      exact absurd (hp _ _ _ _ hpx) (Advanced.irrefl _)
    · rename_i r2 _ _ _ hadv _
      have hr : Advanced r2 it := by
        cases hcur with
        | stay e => exact e ▸ hadv
        | moved e => exact hadv.trans e
      obtain ⟨h1, h2, -⟩ := ih _ _ _ heq
      exact ⟨h1, fun _ => h2 hr, fun _ => h2 hr⟩

/-- if `p` always consumes input on success, the push fold loop never reports an error, stays
advanced once advanced, and advances whenever the accumulator changed -/
@[spec] theorem Spec.efoldlP [Iterators.Finite ι Id]
  (init : Array α) (p : ParserT ε ι τ Id α)
  (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.efoldlP (fun y x => pure (y.push x)) init p)
        (fun s => s.it = it ∧ s.rest = it)
        (fun r s => s.it = it ∧ r.2.isNone
          ∧ (ParseIt.efoldlP (fun (y : Array α ) x => pure (y.push x)) init p s.it = .ok s.rest s.p r)
          ∧ (r.1 ≠ init → Advanced s.rest s.it))
        (fun _ => False) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, hrest⟩
    obtain ⟨sit, srest, sp⟩ := s
    dsimp only at hit hrest ⊢
    subst hit hrest
    obtain rfl := Progress.eq_refl sp
    obtain ⟨rest, h, x, hx⟩ := efoldlP_eq_ok (fun y x => pure (y.push x)) p srest init
    rw [hx]
    simp only [pushResult_ok, Progress.refl_eq, Progress.trans_refl']
    have hx' := hx
    simp only [ParseIt.efoldlP] at hx'
    obtain ⟨h1, -, h3⟩ := efoldlP.loop_push_advanced _ _ _ _ _ hp hx'
    exact ⟨trivial, by simp [h1], trivial, h3⟩)
