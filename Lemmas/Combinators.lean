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
private theorem nextToken_of_eq [Iterators.Productive ι Id] {β : Sort _} (it : Iter (α := ι) τ)
  (yield : (rest : Iter (α := ι) τ) → Advanced rest it → τ → β) (done : Unit → β) (b)
  (h : nextToken it yield done = b)
    : (∃ (it' : Iter (α := ι) τ) (h : Advanced it' it) (x : τ), yield it' h x = b)
      ∨ done () = b  := by
  fun_induction nextToken <;> grind

/-- efoldlP.loop always returns .ok -/
private theorem efoldlP.loop_eq_ok  [Iterators.Finite ι Id]
  (f : β → α → ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) it y cur (hcur : Progress cur it)
    : ∃ rest h x, ParseIt.efoldlP.loop f p it y cur hcur = .ok rest h x := by
  fun_induction efoldlP.loop f p it y cur hcur
  simp [bind, pure]
  repeat split <;> try grind
  simp_all

/-- If every successful round (`p` followed by the update `f`) consumes input, then the fold loop
remains advanced once `cur` has advanced past `it`, and has advanced past `it` whenever the
accumulator changed. -/
private theorem efoldlP.loop_advanced_of_round [Iterators.Finite ι Id]
  (f : β → α → ParserT ε ι τ Id β) (it cur) (hcur : Progress cur it) (y : β)
  (p : ParserT ε ι τ Id α)
  (hround : ∀ s r₁ h₁ x y r₂ h₂ y', p s = .ok r₁ h₁ x → f y x r₁ = .ok r₂ h₂ y' → Advanced r₂ s)
  {rest h' z}
  (heq : efoldlP.loop f p it y cur hcur = .ok rest h' z)
    : (Advanced cur it → Advanced rest it) ∧ (z.1 ≠ y → Advanced rest it) := by
  fun_induction efoldlP.loop f p it y cur hcur
  rename_i s y cur hcur ih
  simp only [bind, pure] at heq
  split at heq
  · cases heq; exact ⟨id, fun h => absurd rfl h⟩
  · rename_i hpx
    split at heq
    · cases heq; exact ⟨id, fun h => absurd rfl h⟩
    · rename_i r1 h1 x _ r2 h2 y' hfy
      have ha : Advanced r2 cur := hround _ _ _ _ _ _ _ _ hpx hfy
      split at heq
      · rename_i e _
        subst e
        exact absurd ha (Advanced.irrefl _)
      · rename_i hadv _
        have hr : Advanced r2 it := by
          cases hcur with
          | stay e => exact e ▸ hadv
          | moved e => exact hadv.trans e
        obtain ⟨h2', -⟩ := ih _ _ _ heq
        exact ⟨fun _ => h2' hr, fun _ => h2' hr⟩

/-- If `p` always consumes input on success, then the fold loop remains advanced once `cur` has
advanced past `it`, and has advanced past `it` whenever the accumulator changed. -/
private theorem efoldlP.loop_advanced [Iterators.Finite ι Id] (f : β → α → ParserT ε ι τ Id β)
  (it cur) (hcur : Progress cur it) (y : β) (p : ParserT ε ι τ Id α)
  (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s) {rest h' z}
  (heq : efoldlP.loop f p it y cur hcur = .ok rest h' z)
    : (Advanced cur it → Advanced rest it) ∧ (z.1 ≠ y → Advanced rest it) := by
  refine efoldlP.loop_advanced_of_round f it cur hcur y p ?_ heq
  intro s r₁ h₁ x y r₂ h₂ y' hpx _
  have ha := hp _ _ _ _ hpx
  cases h₂ with
  | stay e => exact e ▸ ha
  | moved e => exact e.trans ha

/-- If the fold loop reports an error, then that error was produced by a failed update `f`. -/
private theorem efoldlP.loop_error [Iterators.Finite ι Id] (f : β → α → ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (it cur) (hcur : Progress cur it) (y : β) {rest h' z e}
  (heq : efoldlP.loop f p it y cur hcur = .ok rest h' z) (he : z.2 = some e)
    : ∃ y x s, f y x s = .error e := by
  fun_induction efoldlP.loop f p it y cur hcur
  rename_i y cur hcur ih
  simp only [bind, pure] at heq
  split at heq
  · cases heq; cases he
  · split at heq
    · rename_i hfy
      cases heq; cases he
      exact ⟨_, _, _, hfy⟩
    · split at heq
      · cases heq; cases he
      · exact ih _ _ _ heq

/-- The accumulator invariant `P` is preserved by the fold loop if every successful update preserves it. -/
private theorem efoldlP.loop_invariant [Iterators.Finite ι Id] (f : β → α → ParserT ε ι τ Id β)
  (P : β → Prop) (p : ParserT ε ι τ Id α)
  (hf : ∀ y x s rest h y', (∃ s₀ r₀ h₀, p s₀ = .ok r₀ h₀ x) → f y x s = .ok rest h y' → P y → P y')
  (it cur) (hcur : Progress cur it) (y : β) (hy : P y) {rest h' z}
  (heq : efoldlP.loop f p it y cur hcur = .ok rest h' z)
    : P z.1 := by
  fun_induction efoldlP.loop f p it y cur hcur
  rename_i y cur hcur ih
  simp only [bind, pure] at heq
  split at heq
  · cases heq; exact hy
  · rename_i hpx
    split at heq
    · cases heq; exact hy
    · rename_i hfy
      have hy' := hf _ _ _ _ _ _ ⟨_, _, _, hpx⟩ hfy hy
      split at heq
      · cases heq; exact hy'
      · exact ih _ _ _ hy' heq

/-- if `p` always consumes input on success, the push fold loop never reports an error, stays
advanced once advanced, and advances whenever the accumulator changed -/
private theorem efoldlP_of_eq [Iterators.Finite ι Id]
  (init : Array α) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α × Option ε))}
  (h : (efoldlP (fun y x => pure (y.push x)) init p : Parser ε ι τ (Array α × Option ε)) it = r)
    : ∃ (it' : Iter (α := ι) τ) (a : Array α) (e : Option ε) (pr : Progress it' it),
        r = .ok it' pr (a, e)
        ∧ (∀ x ∈ a, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ init
            → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
            → Advanced it' it) := by
  obtain ⟨rest, h', ⟨a, e⟩, hx⟩ :=
    efoldlP.loop_eq_ok (fun y x => pure (y.push x)) p it init it (.refl it)
  refine ⟨rest, a, e, h', h ▸ hx, ?_, fun hne hp => ?_⟩
  · refine efoldlP.loop_invariant _
      (fun y => ∀ x ∈ y, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x) p ?_ it it _ init
      (fun x hx => .inl hx) hx
    intro y x s rest h y' hpx hf hy
    simp only [pure] at hf
    cases hf
    intro z hz
    rcases Array.mem_push.mp hz with hz | rfl
    · exact hy z hz
    · exact .inr hpx
  · exact (efoldlP.loop_advanced _ _ _ _ _ _ hp hx).2 hne

/-- if `p` always consumes input on success, the push fold loop never reports an error, stays
advanced once advanced, and advances whenever the accumulator changed -/
private theorem foldlP_of_eq [Iterators.Finite ι Id]
  (init : Array α) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (foldlP (fun y x => pure (y.push x)) init p : Parser ε ι τ (Array α)) it = r)
    : ∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a
        ∧ (∀ x ∈ a, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ init
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it) := by
  obtain ⟨it', a, e, q, hx, hmem, hne⟩ := efoldlP_of_eq init p it rfl
  refine ⟨it', a, q, ?_, hmem, hne⟩
  subst h
  simp only [ParseIt.foldlP, Functor.map] at hx ⊢
  rw [hx]
  cases q <;> simp only [bind, Function.comp, pure, Progress.refl_eq, Progress.refl_trans']

/-- `foldlM f init p` never fails. Its result satisfies every invariant `P` that holds for `init`
and is preserved by `f` on the outputs of `p`, and if `p` always consumes input on success, it has
consumed input whenever the result differs from `init`. -/
private theorem foldlM_of_eq {β : Type u} [Iterators.Finite ι Id]
  (f : β → α → Id β) (init : β) (p : ParserT ε ι τ Id α) (P : β → Prop)
  (hinit : P init) (hf : ∀ y x, (∃ s rest h, p s = .ok rest h x) → P y → P (f y x))
  (it : Iter (α := ι) τ) {r : Id (Result ε it β)}
  (h : (foldlM f init p : Parser ε ι τ β) it = r)
    : ∃ (it' : Iter (α := ι) τ) (b : β) (pr : Progress it' it),
        r = .ok it' pr b ∧ P b
        ∧ (b ≠ init
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it) := by
  obtain ⟨rest, h', ⟨b, e⟩, hx⟩ :=
    efoldlP.loop_eq_ok (fun y x => (monadLift (f y x) : ParserT ε ι τ Id β)) p it init it (.refl it)
  refine ⟨rest, b, h', ?_, ?_, fun hne hp => ?_⟩
  · subst h
    simp only [ParseIt.foldlM, ParseIt.foldlP, ParseIt.efoldlP, Functor.map]
    rw [hx]
    cases h' <;> simp only [bind, Function.comp, pure, Progress.refl_eq, Progress.refl_trans']
  · refine efoldlP.loop_invariant _ P p ?_ it it _ init hinit hx
    intro y x s rest h y' hpx hfy hy
    simp only [monadLift, MonadLiftT.monadLift, pure] at hfy
    cases hfy
    exact hf y x hpx hy
  · exact (efoldlP.loop_advanced _ _ _ _ _ _ hp hx).2 hne

private theorem endByCore_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (init : Array α) (strict : Bool)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (endByCore sep p init strict : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a
        ∧ (∀ x ∈ a, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ init
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (strict = true ∧ (∃ e, r = .error e ∧ ∃ it'', sep it'' = .error e)) := by
  subst h
  obtain ⟨rest, h', ⟨a, e⟩, hx⟩ :=
    efoldlP.loop_eq_ok (fun xs x => sep *> pure (xs.push x)) p it init it (.refl it)
  have hadv := fun hp => efoldlP.loop_advanced _ _ _ _ _ _ hp hx
  have hmem : ∀ x ∈ a, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x := by
    refine efoldlP.loop_invariant _
      (fun y => ∀ x ∈ y, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x) p ?_ it it _ init
      (fun x hx => .inl hx) hx
    intro y x s rest h y' hpx hf hy
    simp only [SeqRight.seqRight, bind, pure] at hf
    split at hf <;> cases hf
    intro z hz
    rcases Array.mem_push.mp hz with hz | rfl
    · exact hy z hz
    · exact .inr hpx
  have hsep : ∀ e', e = some e' → ∃ it'', sep it'' = .error e' := by
    intro e' he
    obtain ⟨y, x, s, hf⟩ := efoldlP.loop_error _ _ _ _ _ _ hx he
    simp only [SeqRight.seqRight, bind, pure] at hf
    split at hf <;> cases hf
    exact ⟨_, by assumption⟩
  simp only [endByCore, ParseIt.efoldlP, bind] at hx ⊢
  rw [hx]
  cases e <;> cases strict <;> simp [pure, throw, throwThe, MonadExceptOf.throw] <;> grind

private theorem endBy_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (endBy sep p strict : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a
        ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ #[]
           → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (strict = true ∧ (∃ e, r = .error e ∧ ∃ it'', sep it'' = .error e)) := by
  rcases endByCore_of_eq sep p #[] strict it h with ⟨it', a, pr, hr, hmem, hne⟩ | he
  · refine .inl ⟨it', a, pr, hr, fun x hx => ?_, hne⟩
    rcases hmem x hx with hx | hx
    · simp at hx
    · exact hx
  · exact .inr he

/-- `endByCore` only pushes onto `init`, so a successful result is at least as large. -/
private theorem endByCore_size [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (init : Array α) (strict : Bool)
  (it : Iter (α := ι) τ) {it' pr a}
  (h : (endByCore sep p init strict : Parser ε ι τ (Array α)) it = .ok it' pr a)
    : init.size ≤ a.size := by
  obtain ⟨rest, h', ⟨b, e⟩, hx⟩ :=
    efoldlP.loop_eq_ok (fun xs x => sep *> pure (xs.push x)) p it init it (.refl it)
  have hb : init.size ≤ b.size := by
    refine efoldlP.loop_invariant _ (fun y => init.size ≤ y.size) p ?_ it it _ init
      (Nat.le_refl _) hx
    intro y x s rest h y' _ hf hy
    simp only [SeqRight.seqRight, bind, pure] at hf
    split at hf <;> cases hf
    simp; omega
  simp only [endByCore, ParseIt.efoldlP, bind] at hx h
  rw [hx] at h
  cases e <;> cases strict <;> simp [pure, throw, throwThe, MonadExceptOf.throw] at h <;> grind

/-- `endBy1 sep p` either succeeds with a nonempty array (advancing if `p` always consumes input),
fails because the first `p <* sep` failed, or, when `strict`, fails because a later `sep` failed. -/
private theorem endBy1_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (endBy1 sep p strict : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a ∧ 0 < a.size
        ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (∃ e, (p <* sep : Parser ε ι τ α) it = .error e ∧ r = .error e)
      ∨ (strict = true ∧ ∃ e, r = .error e ∧ ∃ it'', sep it'' = .error e) := by
  subst h
  simp only [endBy1, bind, SeqLeft.seqLeft]
  cases hp1 : p it with
  | error e => exact .inr (.inl ⟨e, rfl, rfl⟩)
  | ok r1 h1 x =>
    cases hs : sep r1 with
    | error e => simp only [pure, hs]; exact .inr (.inl ⟨e, rfl, rfl⟩)
    | ok r2 h2 _ =>
      simp only [pure, hs]
      rcases endByCore_of_eq sep p #[x] strict r2 rfl with
        ⟨it', a, pr, he, hmem, -⟩ | ⟨hst, e, he, hsep⟩
      · have hsz := endByCore_size sep p #[x] strict r2 he
        rw [he]
        refine .inl ⟨it', a, _, rfl, by simp at hsz; omega, fun z hz => ?_, fun hp => ?_⟩
        · rcases hmem z hz with hz | hz
          · simp at hz; subst hz; exact ⟨_, _, _, hp1⟩
          · exact hz
        have ha := hp _ _ _ _ hp1
        have hr2 : Advanced r2 it := by
          cases h2 with
          | stay e => exact e ▸ ha
          | moved e => exact e.trans ha
        cases pr with
        | stay e => exact e ▸ hr2
        | moved e => exact e.trans hr2
      · rw [he]
        exact .inr (.inr ⟨hst, e, rfl, hsep⟩)

private theorem sepByCore_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (init : Array α) (strict : Bool)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (sepByCore sep p init strict : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a
        ∧ (∀ x ∈ a, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ init
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (strict = true ∧ (∃ e, r = .error e ∧ ∃ it'', p it'' = .error e)) := by
  subst h
  obtain ⟨rest, h', ⟨a, e⟩, hx⟩ :=
    efoldlP.loop_eq_ok (fun xs _ => (xs.push ·) <$> p) sep it init it (.refl it)
  have hadv := fun (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s) =>
    efoldlP.loop_advanced_of_round _ _ _ _ _ _ (fun s r₁ h₁ x y r₂ h₂ y' _ hfy => by
      simp only [Functor.map, bind, pure] at hfy
      split at hfy <;> cases hfy
      rename_i hpz
      have ha := hp _ _ _ _ hpz
      cases h₁ with
      | stay e => exact e ▸ ha
      | moved e => exact ha.trans e) hx
  have hmem : ∀ x ∈ a, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x := by
    refine efoldlP.loop_invariant _
      (fun y => ∀ x ∈ y, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x) sep ?_ it it _ init
      (fun x hx => .inl hx) hx
    intro y x s rest h y' _ hf hy
    simp only [Functor.map, bind, pure] at hf
    split at hf <;> cases hf
    rename_i hpz
    intro z hz
    rcases Array.mem_push.mp hz with hz | rfl
    · exact hy z hz
    · exact .inr ⟨_, _, _, hpz⟩
  have hperr : ∀ e', e = some e' → ∃ it'', p it'' = .error e' := by
    intro e' he
    obtain ⟨y, x, s, hf⟩ := efoldlP.loop_error _ _ _ _ _ _ hx he
    simp only [Functor.map, bind, pure] at hf
    split at hf <;> cases hf
    exact ⟨_, by assumption⟩
  simp only [sepByCore, ParseIt.efoldlP, bind] at hx ⊢
  rw [hx]
  cases e <;> cases strict <;> simp [pure, throw, throwThe, MonadExceptOf.throw] <;> grind

/-- `sepByCore` only pushes onto `init`, so a successful result is at least as large. -/
private theorem sepByCore_size [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (init : Array α) (strict : Bool)
  (it : Iter (α := ι) τ) {it' pr a}
  (h : (sepByCore sep p init strict : Parser ε ι τ (Array α)) it = .ok it' pr a)
    : init.size ≤ a.size := by
  obtain ⟨rest, h', ⟨b, e⟩, hx⟩ :=
    efoldlP.loop_eq_ok (fun xs _ => (xs.push ·) <$> p) sep it init it (.refl it)
  have hb : init.size ≤ b.size := by
    refine efoldlP.loop_invariant _ (fun y => init.size ≤ y.size) sep ?_ it it _ init
      (Nat.le_refl _) hx
    intro y x s rest h y' _ hf hy
    simp only [Functor.map, bind, pure] at hf
    split at hf <;> cases hf
    simp; omega
  simp only [sepByCore, ParseIt.efoldlP, bind] at hx h
  rw [hx] at h
  cases e <;> cases strict <;> simp [pure, throw, throwThe, MonadExceptOf.throw] at h <;> grind

private theorem sepBy_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (sepBy sep p strict : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a
        ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ #[]
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (strict = true ∧ (∃ e, r = .error e ∧ ∃ it'', p it'' = .error e)) := by
  subst h
  simp only [sepBy, bind]
  rcases option?_of_eq p it rfl with ⟨it1, x, p1, hr, hx⟩ | ⟨e, hr, hx⟩
  · rw [hr]
    simp only []
    rcases sepByCore_of_eq sep p #[x] strict it1 rfl with ⟨it', a, pr, he, hmem, -⟩ | ⟨hst, e, he⟩
    · rw [he]
      refine .inl ⟨it', a, _, rfl, fun z hz => ?_, fun _ hp => ?_⟩
      · rcases hmem z hz with hz | hz
        · simp at hz; subst hz; exact ⟨_, _, _, hx⟩
        · exact hz
      have ha := hp _ _ _ _ hx
      cases pr with
      | stay e => exact e ▸ ha
      | moved e => exact e.trans ha
    · rw [he.1]
      exact .inr ⟨hst, e, rfl, he.2⟩
  · rw [hr]
    exact .inl ⟨it, #[], _, rfl, by simp, by simp⟩

private theorem sepBy1_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (sepBy1 sep p strict : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : Array α) (pr : Progress it' it),
        r = .ok it' pr a ∧ 0 < a.size
        ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (a ≠ #[]
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (∃ e, p it = .error e ∧ r = .error e)
      ∨ (strict = true ∧ (∃ e, r = .error e ∧ ∃ it'', p it'' = .error e)) := by
  subst h
  simp only [sepBy1, bind]
  cases hp1 : p it with
  | error e => exact .inr (.inl ⟨e, rfl, rfl⟩)
  | ok r1 h1 x =>
    simp only []
    rcases sepByCore_of_eq sep p #[x] strict r1 rfl with
      ⟨it', a, pr, he, hmem, -⟩ | ⟨hst, e, he, hperr⟩
    · have hsz := sepByCore_size sep p #[x] strict r1 he
      rw [he]
      refine .inl ⟨it', a, _, rfl, by simp at hsz; omega, fun z hz => ?_, fun _ hp => ?_⟩
      · rcases hmem z hz with hz | hz
        · simp at hz; subst hz; exact ⟨_, _, _, hp1⟩
        · exact hz
      have ha := hp _ _ _ _ hp1
      cases pr with
      | stay e => exact e ▸ ha
      | moved e => exact e.trans ha
    · rw [he]
      exact .inr (.inr ⟨hst, e, rfl, hperr⟩)

/-- `tokenMap f` reads one token `t` and succeeds with `a` when `f t = some a`, consuming input.
It fails with `Error.unexpected it none` at end of input, or with `Error.unexpected it (some t)`
when `f t = none`. -/
private theorem tokenMap_of_eq [Iterators.Productive ι Id] [Error ε ι τ] (f : τ → Option α)
  (it : Iter (α := ι) τ) {r} (h : (ParseIt.tokenMap f : Parser ε ι τ α) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : α) (h : Advanced it' it) (t : τ),
          f t = some a ∧ r = .ok it' (.moved h) a)
      ∨ (∃ e : ε, r = .error e ∧ (e = (Error.unexpected it none)
          ∨ ∃ (t : τ), f t = none ∧ e = (Error.unexpected it (some t)))) := by
  simp only [ParseIt.tokenMap, pure] at h
  rcases nextToken_of_eq _ _ _ _ h with ⟨it', h', x, hx⟩ | hx
  · split at hx <;> subst hx
    · exact .inl ⟨_, _, h', x, ‹_›, rfl⟩
    · exact .inr ⟨_, rfl, .inr ⟨x, ‹_›, rfl⟩⟩
  · subst hx
    exact .inr ⟨_, rfl, .inl rfl⟩

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
    rintro ⟨sit, srest, sp⟩ ⟨hit, hrest⟩
    dsimp only at hit hrest ⊢
    subst hit hrest
    generalize hr : (ParseIt.tokenMap f : Parser ε ι τ α) srest = r
    rcases tokenMap_of_eq f srest hr with ⟨it', a, h, t, ht, rfl⟩ | ⟨e, rfl, he⟩
    · cases sp <;> exact ⟨rfl, ⟨t, ht⟩, rfl, h⟩
    · exact he)

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

/-- The loop of `tokenArray` over `l`, starting from the accumulator `acc`: on success it returns
`acc ++ l.toArray` and consumes input whenever `l` is non-empty; any failure is an `unexpected`
error. -/
private theorem tokenArray_loop [Iterators.Productive ι Id] [Error ε ι τ] [BEq τ] [LawfulBEq τ]
  (l : List τ) (acc : Array τ) (it : Iter (α := ι) τ) :
    match (forIn l acc (fun tk (r : Array τ) => do
        let x ← (token tk : Parser ε ι τ τ)
        pure (ForInStep.yield (r.push x))) : Parser ε ι τ (Array τ)) it with
    | .ok rest _ r => r = acc ++ l.toArray ∧ (l ≠ [] → Advanced rest it)
    | .error e => ∃ (it' : Iter (α := ι) τ) (t : Option τ), e = Error.unexpected it' t := by
  induction l generalizing acc it with
  | nil => simp [pure]
  | cons tk l ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have ht := Parser.of_wp_eq _ (Spec.token (ε := ε) tk it) it (by simp [IterWithProgress.refl])
    revert ht
    cases (token tk : Parser ε ι τ τ) it with
    | error e =>
      rintro (rfl | ⟨t, -, rfl⟩)
      · exact ⟨it, none, rfl⟩
      · exact ⟨it, some t, rfl⟩
    | ok rest h x =>
      rintro ⟨-, rfl, -, hadv⟩
      dsimp only
      have := ih (acc.push x) rest
      revert this
      generalize (forIn l (acc.push x) _ : Parser ε ι τ (Array τ)) rest = r
      cases r with
      | error e => exact id
      | ok rest' h' r =>
        rintro ⟨rfl, -⟩
        exact ⟨by simp, fun _ => Progress.advanced_of_trans h' hadv⟩

/-- Evaluation of `tokenArray tks` at `it` in terms of its loop over `tks.toList`. -/
private theorem tokenArray_eq_apply [Iterators.Productive ι Id] [Error ε ι τ] [BEq τ]
  (tks : Array τ) (it : Iter (α := ι) τ) :
    (ParseIt.tokenArray tks : Parser ε ι τ (Array τ)) it =
    match (forIn tks.toList #[] (fun tk (r : Array τ) => do
        let x ← (token tk : Parser ε ι τ τ)
        pure (ForInStep.yield (r.push x))) : Parser ε ι τ (Array τ)) it with
    | .ok rest h r => .ok rest h r
    | .error e => .error e := by
  rw [Array.forIn_toList]
  simp only [ParseIt.tokenArray, Array.emptyWithCapacity_eq, bind, pure]
  split <;> simp_all [Progress.refl_trans']

/-- `tokenArray tks` succeeds with `tks` when the input starts with the tokens of `tks`, consuming
input if `tks` is non-empty; otherwise it fails with an `unexpected` error. -/
@[spec] theorem Spec.tokenArray [Iterators.Productive ι Id] [Iterators.Finite ι Id] [Error ε ι τ]
  [BEq τ] [LawfulBEq τ] (tks : Array τ) (it : Iter (α := ι) τ)
    : Triple (ParseIt.tokenArray tks : Parser ε ι τ (Array τ))
        (fun s => s.it = it ∧ s.rest = it)
        (fun r s => s.it = it ∧ r = tks
                ∧ (ParseIt.tokenArray tks : Parser ε ι τ (Array τ)) s.it = .ok s.rest s.p r
                ∧ (tks ≠ #[] → Advanced s.rest s.it))
        (fun e => ∃ (it' : Iter (α := ι) τ) (t : Option τ), e = Error.unexpected it' t) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, wp, WP.trans, Parser.run, pushResult]
    rintro ⟨it₀, rest, p⟩ ⟨h₁, h₂⟩
    dsimp only at h₁ h₂ ⊢
    subst it₀ rest
    rw [Progress.eq_refl p]
    have hl := tokenArray_loop (ε := ε) tks.toList #[] it
    rw [tokenArray_eq_apply]
    revert hl
    generalize hr : (forIn tks.toList #[] _ : Parser ε ι τ (Array τ)) it = r
    cases r with
    | ok rest h r =>
      rintro ⟨rfl, hl⟩
      refine ⟨rfl, by simp, by simp, fun hne => hl ?_⟩
      simpa using hne
    | error e => exact id)

/-- Evaluation of `tokenList tks` at `it` in terms of `tokenArray tks.toArray`. -/
private theorem tokenList_eq_apply [Iterators.Productive ι Id] [Error ε ι τ] [BEq τ]
  (tks : List τ) (it : Iter (α := ι) τ) :
    (ParseIt.tokenList tks : Parser ε ι τ (List τ)) it =
    match (ParseIt.tokenArray tks.toArray : Parser ε ι τ (Array τ)) it with
    | .ok rest h r => .ok rest h r.toList
    | .error e => .error e := by
  simp only [ParseIt.tokenList, Functor.map, bind, pure, Function.comp]
  split <;> simp_all [Progress.refl_trans']

/-- `tokenList tks` succeeds with `tks` when the input starts with the tokens of `tks`, consuming
input if `tks` is non-empty; otherwise it fails with an `unexpected` error. -/
@[spec] theorem Spec.tokenList [Iterators.Productive ι Id] [Iterators.Finite ι Id] [Error ε ι τ]
  [BEq τ] [LawfulBEq τ] (tks : List τ) (it : Iter (α := ι) τ)
    : Triple (ParseIt.tokenList tks : Parser ε ι τ (List τ))
        (fun s => s.it = it ∧ s.rest = it)
        (fun r s => s.it = it ∧ r = tks
                ∧ (ParseIt.tokenList tks : Parser ε ι τ (List τ)) s.it = .ok s.rest s.p r
                ∧ (tks ≠ [] → Advanced s.rest s.it))
        (fun e => ∃ (it' : Iter (α := ι) τ) (t : Option τ), e = Error.unexpected it' t) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, wp, WP.trans, Parser.run, pushResult]
    rintro ⟨it₀, rest, p⟩ ⟨h₁, h₂⟩
    dsimp only at h₁ h₂ ⊢
    subst it₀ rest
    rw [Progress.eq_refl p]
    have ha := Parser.of_wp_eq _ (Spec.tokenArray (ε := ε) tks.toArray it) it
      (by simp [IterWithProgress.refl])
    rw [tokenList_eq_apply]
    revert ha
    cases (ParseIt.tokenArray tks.toArray : Parser ε ι τ (Array τ)) it with
    | ok rest h r =>
      rintro ⟨-, rfl, -, hadv⟩
      exact ⟨rfl, by simp, by simp, fun hne => hadv (by simpa using hne)⟩
    | error e => exact id)

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

/-- ``foldP`` never reports an error. If `p` always consumes input on success,
  ``foldP`` advances whenever the accumulator changed -/
@[spec] theorem Spec.foldlP [Iterators.Finite ι Id]
  (init : Array α) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldlP (fun y x => pure (y.push x)) init p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun r s => s.it = it
          ∧ (ParseIt.foldlP (fun (y : Array α) x => pure (y.push x)) init p s.it = .ok s.rest s.p r)
          ∧ (∀ x ∈ r, x ∈ init ∨ ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (r ≠ init
              → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest s.it))
        (fun _ => False) :=
  Triple.intro (by
    simp []
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro ⟨sit, srest, sp⟩ ⟨hit, hrest⟩
    dsimp only at hit hrest ⊢
    subst hit hrest
    obtain rfl := Progress.eq_refl sp
    obtain ⟨it', a, q, hf, hne⟩ := foldlP_of_eq init p srest rfl
    rw [hf]
    simp only [pushResult_ok, Progress.refl_eq, Progress.trans_refl']
    exact ⟨trivial, trivial, hne⟩)

/-- `foldlM f init p` never fails. Its result satisfies every invariant `P` that holds for `init`
and is preserved by `f` on the outputs of `p`, and if `p` always consumes input on success, it has
consumed input whenever the result differs from `init`. -/
@[spec] theorem Spec.foldlM {β : Type u} [Iterators.Finite ι Id]
  (f : β → α → Id β) (init : β) (p : ParserT ε ι τ Id α) (P : β → Prop)
  (hinit : P init) (hf : ∀ y x, (∃ s rest h, p s = .ok rest h x) → P y → P (f y x))
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldlM f init p : Parser ε ι τ β)
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it
          ∧ (ParseIt.foldlM f init p : Parser ε ι τ β) s.it = .ok s.rest s.p b
          ∧ P b
          ∧ (b ≠ init
              → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest s.it))
        (fun _ => False) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro ⟨sit, srest, sp⟩ ⟨hit, hrest⟩
    dsimp only at hit hrest ⊢
    subst hit hrest
    obtain rfl := Progress.eq_refl sp
    obtain ⟨it', b, q, hr, hP, hne⟩ := foldlM_of_eq f init p P hinit hf srest rfl
    rw [hr]
    simp only [pushResult_ok, Progress.refl_eq, Progress.trans_refl']
    exact ⟨trivial, trivial, hP, hne⟩)

/-! Specs for the remaining combinators -/

variable {β γ : Type u}

/-- A spec for `x` started at `it` from a description of `x it`: on success the final state is
exactly what `x it` returns and satisfies `Q`, and on failure the error satisfies `E`. -/
theorem Spec.of_apply [Iterators.Finite ι Id] (x : Parser ε ι τ β) (it : Iter (α := ι) τ)
  (Q : β → IterWithProgress ι τ → Prop) (E : ε → Prop)
  (h : match x it with | .ok rest pr b => Q b ⟨it, rest, pr⟩ | .error e => E e)
    : Triple x (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it ∧ x s.it = .ok s.rest s.p b ∧ Q b s) E :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, wp, WP.trans, Parser.run, pushResult]
    rintro ⟨it₀, rest, p⟩ ⟨h₁, h₂⟩
    dsimp only at h₁ h₂ ⊢
    subst it₀ rest
    rw [Progress.eq_refl p]
    revert h
    cases x it <;> simp)

/-- `foldl f` is `foldlM` with the pure update `f`. -/
private theorem foldl_eq_foldlM [Iterators.Finite ι Id] (f : β → α → β) (init : β) (p : ParserT ε ι τ Id α) :
    (foldl f init p : Parser ε ι τ β) = foldlM (fun y x => (f y x : Id β)) init p := rfl

/-- `foldl f init p` never fails. Its result satisfies every invariant `P` that holds for `init`
and is preserved by `f` on the outputs of `p`, and if `p` always consumes input on success, it has
consumed input whenever the result differs from `init`. -/
private theorem foldl_of_eq [Iterators.Finite ι Id]
  (f : β → α → β) (init : β) (p : ParserT ε ι τ Id α) (P : β → Prop)
  (hinit : P init) (hf : ∀ y x, (∃ s rest h, p s = .ok rest h x) → P y → P (f y x))
  (it : Iter (α := ι) τ) {r : Id (Result ε it β)}
  (h : (foldl f init p : Parser ε ι τ β) it = r)
    : ∃ (it' : Iter (α := ι) τ) (b : β) (pr : Progress it' it),
        r = .ok it' pr b ∧ P b
        ∧ (b ≠ init
           → (hp : ∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it) := by
  rw [foldl_eq_foldlM] at h
  exact foldlM_of_eq _ init p P hinit hf it h

/-- `foldlN n f init p` either folds `f` over exactly `n` outputs `xs` of `p`, consuming input
when `n > 0` and `p` always consumes input, or fails with an error of `p`. -/
private theorem foldlN_of_eq (n : Nat) (f : β → α → β) (init : β) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) {r : Id (Result ε it β)}
  (h : (foldlN n f init p : Parser ε ι τ β) it = r)
    : (∃ (it' : Iter (α := ι) τ) (pr : Progress it' it) (xs : List α),
        r = .ok it' pr (xs.foldl f init) ∧ xs.length = n
        ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (0 < n
           → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (∃ e, r = .error e ∧ ∃ it'', p it'' = .error e) := by
  subst h
  induction n generalizing init it with
  | zero => exact .inl ⟨it, _, [], rfl, rfl, by simp, by simp⟩
  | succ n ih =>
    simp only [foldlN, bind]
    cases hp1 : p it with
    | error e => exact .inr ⟨e, rfl, it, hp1⟩
    | ok r1 h1 x =>
      dsimp only
      rcases ih (f init x) r1 with ⟨it', pr, xs, hr, hlen, hmem, -⟩ | ⟨e, hr, he⟩
      · rw [hr]
        refine .inl ⟨it', _, x :: xs, rfl, by simp [hlen], ?_, fun _ hp => ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ⟨_, _, _, hp1⟩
          · exact hmem z hz
        · exact Progress.advanced_of_trans pr (hp _ _ _ _ hp1)
      · rw [hr]
        exact .inr ⟨e, rfl, he⟩

/-- `foldlUpTo n f init p` never fails: it folds `f` over at most `n` outputs `xs` of `p`,
consuming input when `xs` is non-empty and `p` always consumes input. -/
private theorem foldlUpTo_of_eq (n : Nat) (f : β → α → β) (init : β) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) {r : Id (Result ε it β)}
  (h : (foldlUpTo n f init p : Parser ε ι τ β) it = r)
    : ∃ (it' : Iter (α := ι) τ) (pr : Progress it' it) (xs : List α),
        r = .ok it' pr (xs.foldl f init) ∧ xs.length ≤ n
        ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (xs ≠ []
           → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it) := by
  subst h
  induction n generalizing init it with
  | zero => exact ⟨it, _, [], rfl, by simp, by simp, by simp⟩
  | succ n ih =>
    simp only [foldlUpTo, bind]
    rcases option?_of_eq p it rfl with ⟨r1, x, h1, hr, hx⟩ | ⟨e, hr, hx⟩
    · rw [hr]
      dsimp only
      obtain ⟨it', pr, xs, hr', hlen, hmem, -⟩ := ih (f init x) r1
      rw [hr']
      refine ⟨it', _, x :: xs, rfl, by simp; omega, ?_, fun _ hp => ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨_, _, _, hx⟩
        · exact hmem z hz
      · exact Progress.advanced_of_trans pr (hp _ _ _ _ hx)
    · rw [hr]
      exact ⟨it, _, [], rfl, by simp, by simp, by simp⟩

/-- The loop of `foldlUntil` either folds `f` over outputs `xs` of `p` and ends with an output `z`
of `stop`, or fails with an error of `p` or of `stop`. -/
private theorem foldlUntil.loop_of_eq [Iterators.Finite ι Id] (f : γ → α → γ)
  (stop : ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) (y : γ) (cur : Iter (α := ι) τ) (hcur : Progress cur it)
  {r : Id (Result ε it (γ × β))}
  (h : foldlUntil.loop f stop p it y cur hcur = r)
    : (∃ (it' : Iter (α := ι) τ) (pr : Progress it' it) (xs : List α) (z : β),
        r = .ok it' pr (xs.foldl f y, z)
        ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (∃ it' it'' pr, stop it' = .ok it'' pr z))
      ∨ (∃ e, r = .error e ∧ ((∃ it'', p it'' = .error e) ∨ (∃ it'', stop it'' = .error e))) := by
  subst h
  fun_induction foldlUntil.loop f stop p it y cur hcur with
  | case1 y cur hcur ih =>
    simp only [bind, pure]
    cases hs : stop cur with
    | ok rest h z => exact .inl ⟨rest, _, [], z, rfl, by simp, ⟨_, _, _, hs⟩⟩
    | error e =>
      dsimp only
      cases hp : p cur with
      | error e' => exact .inr ⟨e', rfl, .inl ⟨_, hp⟩⟩
      | ok rest hpr x =>
        cases hpr with
        | stay h => exact .inr ⟨e, rfl, .inr ⟨_, hs⟩⟩
        | moved h =>
          dsimp only
          rcases ih rest h x with ⟨it', pr, xs, z, hr, hmem, hz⟩ | he
          · rw [hr]
            refine .inl ⟨it', pr, x :: xs, z, rfl, ?_, hz⟩
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact ⟨_, _, _, hp⟩
            · exact hmem w hw
          · exact .inr he

/-- `foldr f p q` at `it` either returns `xs.foldr f y` for outputs `xs` of `p` and an output `y`
of `q`, or fails with the error of `q` at `it`. -/
private theorem foldr_of_eq [Iterators.Finite ι Id] (f : α → β → β)
  (p : ParserT ε ι τ Id α) (q : ParserT ε ι τ Id β)
  (it : Iter (α := ι) τ) {r : Id (Result ε it β)}
  (h : (foldr f p q : Parser ε ι τ β) it = r)
    : (∃ (it' : Iter (α := ι) τ) (pr : Progress it' it) (xs : List α) (y : β),
        r = .ok it' pr (xs.foldr f y)
        ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (∃ it' it'' pr, q it' = .ok it'' pr y))
      ∨ (∃ e, r = .error e ∧ q it = .error e) := by
  subst h
  fun_induction foldr f p q it with
  | case1 it ih =>
    have hq : (∃ (it' : Iter (α := ι) τ) (pr : Progress it' it) (xs : List α) (y : β),
          q it = .ok it' pr (xs.foldr f y)
          ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (∃ it' it'' pr, q it' = .ok it'' pr y))
        ∨ (∃ e, q it = .error e ∧ q it = .error e) := by
      cases hq : q it with
      | ok rest h y => exact .inl ⟨rest, h, [], y, rfl, by simp, ⟨_, _, _, hq⟩⟩
      | error e => exact .inr ⟨e, rfl, rfl⟩
    simp only [bind, pure]
    cases hp : p it with
    | error e => exact hq
    | ok rest pr x =>
      cases pr with
      | moved h =>
        dsimp only
        rcases ih rest h with ⟨it', pr', xs, y, hr, hmem, hy⟩ | ⟨e, hr, -⟩
        · rw [hr]
          refine .inl ⟨it', _, x :: xs, y, rfl, ?_, hy⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact ⟨_, _, _, hp⟩
          · exact hmem w hw
        · rw [hr]
          exact hq
      | stay h =>
        dsimp only
        cases hq' : q rest with
        | ok rest' h' y =>
          refine .inl ⟨rest', _, [x], y, rfl, ?_, ⟨_, _, _, hq'⟩⟩
          intro w hw
          rcases List.mem_singleton.mp hw with rfl
          exact ⟨_, _, _, hp⟩
        | error e => exact hq

/-- Folding `Array.push` over a list appends the list to the accumulator. -/
private theorem foldl_push (xs : List α) (acc : Array α) : xs.foldl Array.push acc = acc ++ xs.toArray := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- `take n p` returns exactly `n` outputs of `p`, consuming input when `n > 0` and `p` always
consumes input; on failure the error is an error of `p`. -/
@[spec] theorem Spec.take [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.take n p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.take n p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ a.size = n ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (0 < n → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases foldlN_of_eq n Array.push _ p it (r := (ParseIt.take n p : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', pr, xs, hr, hlen, hmem, hadv⟩ | ⟨e, hr, he⟩
    · rw [hr]
      simp only [foldl_push, Array.emptyWithCapacity_eq, List.append_toArray, List.nil_append]
      refine ⟨by simp [hlen], fun x hx => hmem x (by simpa using hx), hadv⟩
    · rw [hr]
      exact he)

/-- Folding the successor over a list adds its length to the accumulator. -/
private theorem foldl_succ_val (xs : List α) (acc : Natᵤ.{u}) :
    (xs.foldl (fun (n : Natᵤ.{u}) (_ : α) => (⟨n.val + 1⟩ : Natᵤ.{u})) acc).val = acc.val + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

/-- `take n p` either returns `n` outputs of `p`, consuming input when `n > 0` and `p` always
consumes input, or fails with an error of `p`. -/
private theorem take_of_eq (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) {r : Id (Result ε it (Array α))}
  (h : (ParseIt.take n p : Parser ε ι τ (Array α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (pr : Progress it' it) (a : Array α),
        r = .ok it' pr a ∧ a.size = n
        ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
        ∧ (0 < n
           → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (∃ e, r = .error e ∧ ∃ it'', p it'' = .error e) := by
  rcases foldlN_of_eq n Array.push _ p it h with ⟨it', pr, xs, hr, hlen, hmem, hadv⟩ | he
  · refine .inl ⟨it', pr, _, hr, by simp [hlen], fun x hx => hmem x ?_, hadv⟩
    simpa [foldl_push] using hx
  · exact .inr he

/-- `drop n p` either succeeds, consuming input when `n > 0` and `p` always consumes input, or
fails with an error of `p`. -/
private theorem drop_of_eq (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ) {r : Id (Result ε it Unitᵤ)}
  (h : (ParseIt.drop n p : Parser ε ι τ Unitᵤ) it = r)
    : (∃ (it' : Iter (α := ι) τ) (pr : Progress it' it),
        r = .ok it' pr ⟨⟩
        ∧ (0 < n
           → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
           → Advanced it' it))
      ∨ (∃ e, r = .error e ∧ ∃ it'', p it'' = .error e) := by
  rcases foldlN_of_eq n _ _ p it h with ⟨it', pr, xs, hr, -, -, hadv⟩ | he
  · exact .inl ⟨it', pr, hr, hadv⟩
  · exact .inr he

/-- `optional x` never fails. -/
private theorem optional_of_eq (x : Parser ε ι τ α) (it : Iter (α := ι) τ) {r}
  (h : (ParseIt.optional x : Parser ε ι τ Unitᵤ) it = r)
    : ∃ (it' : Iter (α := ι) τ) (pr : Progress it' it), r = .ok it' pr ⟨⟩ := by
  rcases optionD_of_eq ((x *> pure (⟨⟩ : Unitᵤ)) : Parser ε ι τ Unitᵤ) (⟨⟩ : Unitᵤ) it h with ⟨it', a, p, hr, -⟩ | ⟨e, hr, -⟩
  · exact ⟨it', p, hr⟩
  · exact ⟨it, _, hr⟩

/-- `foldl f init p` never fails. Its result satisfies every invariant `P` that holds for `init`
and is preserved by `f` on the outputs of `p`, and if `p` always consumes input on success, it has
consumed input whenever the result differs from `init`. -/
@[spec] theorem Spec.foldl [Iterators.Finite ι Id]
  (f : β → α → β) (init : β) (p : ParserT ε ι τ Id α) (P : β → Prop)
  (hinit : P init) (hf : ∀ y x, (∃ s rest h, p s = .ok rest h x) → P y → P (f y x))
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldl f init p : Parser ε ι τ β)
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it ∧ (ParseIt.foldl f init p : Parser ε ι τ β) s.it = .ok s.rest s.p b
          ∧ P b
          ∧ (b ≠ init
              → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', b, pr, hr, hP, hne⟩ :=
      foldl_of_eq f init p P hinit hf it (r := (ParseIt.foldl f init p : Parser ε ι τ β) it) rfl
    rw [hr]
    exact ⟨hP, hne⟩)

/-- `foldr f p q` returns `xs.foldr f y` for outputs `xs` of `p` and an output `y` of `q`; on
failure the error is that of `q` at the start position `it`. -/
@[spec] theorem Spec.foldr [Iterators.Finite ι Id] (f : α → β → β)
  (p : ParserT ε ι τ Id α) (q : ParserT ε ι τ Id β) (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldr f p q : Parser ε ι τ β)
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it ∧ (ParseIt.foldr f p q : Parser ε ι τ β) s.it = .ok s.rest s.p b
          ∧ ∃ (xs : List α) (y : β), b = xs.foldr f y
            ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
            ∧ (∃ it' it'' pr, q it' = .ok it'' pr y))
        (fun e => q it = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases foldr_of_eq f p q it (r := (ParseIt.foldr f p q : Parser ε ι τ β) it) rfl with
      ⟨it', pr, xs, y, hr, hmem, hy⟩ | ⟨e, hr, he⟩
    · rw [hr]
      exact ⟨xs, y, rfl, hmem, hy⟩
    · rw [hr]
      exact he)

/-- `foldlN n f init p` folds `f` over exactly `n` outputs of `p`, consuming input when `n > 0`
and `p` always consumes input; on failure the error is an error of `p`. -/
@[spec] theorem Spec.foldlN [Iterators.Finite ι Id] (n : Nat) (f : β → α → β) (init : β)
  (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldlN n f init p : Parser ε ι τ β)
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it ∧ (ParseIt.foldlN n f init p : Parser ε ι τ β) s.it = .ok s.rest s.p b
          ∧ ∃ xs : List α, b = xs.foldl f init ∧ xs.length = n
            ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
            ∧ (0 < n
                → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
                → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases foldlN_of_eq n f init p it (r := (ParseIt.foldlN n f init p : Parser ε ι τ β) it) rfl with
      ⟨it', pr, xs, hr, hlen, hmem, hadv⟩ | ⟨e, hr, he⟩
    · rw [hr]
      exact ⟨xs, rfl, hlen, hmem, hadv⟩
    · rw [hr]
      exact he)

/-- `foldlUpTo n f init p` never fails: it folds `f` over at most `n` outputs of `p`, consuming
input when it folded at least one and `p` always consumes input. -/
@[spec] theorem Spec.foldlUpTo [Iterators.Finite ι Id] (n : Nat) (f : β → α → β) (init : β)
  (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldlUpTo n f init p : Parser ε ι τ β)
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it ∧ (ParseIt.foldlUpTo n f init p : Parser ε ι τ β) s.it = .ok s.rest s.p b
          ∧ ∃ xs : List α, b = xs.foldl f init ∧ xs.length ≤ n
            ∧ (∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
            ∧ (xs ≠ []
                → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
                → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', pr, xs, hr, hlen, hmem, hadv⟩ :=
      foldlUpTo_of_eq n f init p it (r := (ParseIt.foldlUpTo n f init p : Parser ε ι τ β) it) rfl
    rw [hr]
    exact ⟨xs, rfl, hlen, hmem, hadv⟩)

/-- `foldlUntil f init stop p` folds `f` over outputs of `p` and pairs the result with an output
of `stop`; on failure the error is an error of `p` or of `stop`. -/
@[spec] theorem Spec.foldlUntil [Iterators.Finite ι Id] (f : γ → α → γ) (init : γ)
  (stop : ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.foldlUntil f init stop p : Parser ε ι τ (γ × β))
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it
          ∧ (ParseIt.foldlUntil f init stop p : Parser ε ι τ (γ × β)) s.it = .ok s.rest s.p b
          ∧ (∃ xs : List α, b.1 = xs.foldl f init ∧ ∀ x ∈ xs, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (∃ it' it'' pr, stop it' = .ok it'' pr b.2))
        (fun e => (∃ it'', p it'' = .error e) ∨ (∃ it'', stop it'' = .error e)) :=
  Spec.of_apply _ it _ _ (by
    rcases foldlUntil.loop_of_eq f stop p it init it (.refl it)
        (r := (ParseIt.foldlUntil f init stop p : Parser ε ι τ (γ × β)) it) rfl with
      ⟨it', pr, xs, z, hr, hmem, hz⟩ | ⟨e, hr, he⟩
    · rw [hr]
      exact ⟨⟨xs, rfl, hmem⟩, hz⟩
    · rw [hr]
      exact he)

/-- `takeUpTo n p` never fails: it returns at most `n` outputs of `p`, consuming input when the
result is non-empty and `p` always consumes input. -/
@[spec] theorem Spec.takeUpTo [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.takeUpTo n p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.takeUpTo n p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ a.size ≤ n ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (a ≠ #[] → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', pr, xs, hr, hlen, hmem, hadv⟩ :=
      foldlUpTo_of_eq n Array.push #[] p it (r := (ParseIt.takeUpTo n p : Parser ε ι τ (Array α)) it) rfl
    rw [hr]
    simp only [foldl_push, List.append_toArray, List.nil_append]
    refine ⟨by simpa using hlen, fun x hx => hmem x (by simpa using hx), fun hne => hadv ?_⟩
    rintro rfl
    simp at hne)

/-- `takeMany p` never fails: it returns outputs of `p`, consuming input when the result is
non-empty and `p` always consumes input. -/
@[spec] theorem Spec.takeMany [Iterators.Finite ι Id] (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.takeMany p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.takeMany p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (a ≠ #[] → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', a, pr, hr, hmem, hne⟩ :=
      foldl_of_eq Array.push #[] p (fun y => ∀ x ∈ y, ∃ it' it'' pr, p it' = .ok it'' pr x)
        (by simp) (fun y x hx hy z hz => by
          rcases Array.mem_push.mp hz with hz | rfl
          · exact hy z hz
          · exact hx)
        it (r := (ParseIt.takeMany p : Parser ε ι τ (Array α)) it) rfl
    rw [hr]
    exact ⟨hmem, hne⟩)

/-- `takeMany1 p` returns a non-empty array of outputs of `p`, consuming input when `p` always
consumes input; on failure the error is that of the first `p` at `it`. -/
@[spec] theorem Spec.takeMany1 [Iterators.Finite ι Id] (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.takeMany1 p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.takeMany1 p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ 0 < a.size ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => p it = .error e) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.takeMany1, bind]
    cases hp1 : p it with
    | error e => rfl
    | ok r1 h1 x =>
      dsimp only
      obtain ⟨it', a, pr, hr, ⟨hpos, hmem⟩, -⟩ :=
        foldl_of_eq Array.push #[x] p
          (fun y => 0 < y.size ∧ ∀ x ∈ y, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ⟨by simp, by simpa using ⟨_, _, _, hp1⟩⟩ (fun y x hx hy => ⟨by simp, fun z hz => by
            rcases Array.mem_push.mp hz with hz | rfl
            · exact hy.2 z hz
            · exact hx⟩)
          r1 (r := (ParseIt.foldl Array.push #[x] p : Parser ε ι τ (Array α)) r1) rfl
      rw [hr]
      exact ⟨hpos, hmem, fun hp => Progress.advanced_of_trans pr (hp _ _ _ _ hp1)⟩)

/-- `takeManyN n p` returns at least `n` outputs of `p`, consuming input when `n > 0` and `p`
always consumes input; on failure the error is an error of `p`. -/
@[spec] theorem Spec.takeManyN [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.takeManyN n p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.takeManyN n p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ n ≤ a.size ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (0 < n → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.takeManyN, bind]
    rcases take_of_eq n p it (r := (ParseIt.take n p : Parser ε ι τ (Array α)) it) rfl with
      ⟨r1, h1, xs, hr1, hsz, hmem1, hadv1⟩ | ⟨e, hr1, he⟩
    · rw [hr1]
      dsimp only
      obtain ⟨it', a, pr, hr, ⟨hsz', hmem⟩, -⟩ :=
        foldl_of_eq Array.push xs p
          (fun y => n ≤ y.size ∧ ∀ x ∈ y, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ⟨by omega, hmem1⟩ (fun y x hx hy => ⟨by simp; omega, fun z hz => by
            rcases Array.mem_push.mp hz with hz | rfl
            · exact hy.2 z hz
            · exact hx⟩)
          r1 (r := (ParseIt.foldl Array.push xs p : Parser ε ι τ (Array α)) r1) rfl
      rw [hr]
      exact ⟨hsz', hmem, fun hn hp => Progress.advanced_of_trans pr (hadv1 hn hp)⟩
    · rw [hr1]
      exact he)

/-- `takeUntil stop p` returns outputs of `p` paired with an output of `stop`; on failure the
error is an error of `p` or of `stop`. -/
@[spec] theorem Spec.takeUntil [Iterators.Finite ι Id]
  (stop : ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.takeUntil stop p : Parser ε ι τ (Array α × β))
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it
          ∧ (ParseIt.takeUntil stop p : Parser ε ι τ (Array α × β)) s.it = .ok s.rest s.p b
          ∧ (∀ x ∈ b.1, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (∃ it' it'' pr, stop it' = .ok it'' pr b.2))
        (fun e => (∃ it'', p it'' = .error e) ∨ (∃ it'', stop it'' = .error e)) :=
  Spec.of_apply _ it _ _ (by
    rcases foldlUntil.loop_of_eq Array.push stop p it #[] it (.refl it)
        (r := (ParseIt.takeUntil stop p : Parser ε ι τ (Array α × β)) it) rfl with
      ⟨it', pr, xs, z, hr, hmem, hz⟩ | ⟨e, hr, he⟩
    · rw [hr]
      exact ⟨fun x hx => hmem x (by simpa [foldl_push] using hx), hz⟩
    · rw [hr]
      exact he)

/-- `drop n p` consumes input when `n > 0` and `p` always consumes input; on failure the error
is an error of `p`. -/
@[spec] theorem Spec.drop [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.drop n p : Parser ε ι τ Unitᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.drop n p : Parser ε ι τ Unitᵤ) s.it = .ok s.rest s.p a
          ∧ (0 < n → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases drop_of_eq n p it (r := (ParseIt.drop n p : Parser ε ι τ Unitᵤ) it) rfl with
      ⟨it', pr, hr, hadv⟩ | ⟨e, hr, he⟩
    · rw [hr]
      exact hadv
    · rw [hr]
      exact he)

/-- `dropUpTo n p` never fails. -/
@[spec] theorem Spec.dropUpTo [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.dropUpTo n p : Parser ε ι τ Unitᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.dropUpTo n p : Parser ε ι τ Unitᵤ) s.it = .ok s.rest s.p a
          ∧ True)
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', pr, xs, hr, -⟩ :=
      foldlUpTo_of_eq n _ _ p it (r := (ParseIt.dropUpTo n p : Parser ε ι τ Unitᵤ) it) rfl
    rw [hr]
    trivial)

/-- `dropMany p` never fails. -/
@[spec] theorem Spec.dropMany [Iterators.Finite ι Id] (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.dropMany p : Parser ε ι τ Unitᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.dropMany p : Parser ε ι τ Unitᵤ) s.it = .ok s.rest s.p a
          ∧ True)
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', a, pr, hr, -⟩ := foldl_of_eq _ _ p (fun _ => True) trivial (fun _ _ _ _ => trivial)
      it (r := (ParseIt.dropMany p : Parser ε ι τ Unitᵤ) it) rfl
    rw [hr]
    trivial)

/-- `dropMany1 p` consumes input when `p` always consumes input; on failure the error is that of
the first `p` at `it`. -/
@[spec] theorem Spec.dropMany1 [Iterators.Finite ι Id] (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.dropMany1 p : Parser ε ι τ Unitᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.dropMany1 p : Parser ε ι τ Unitᵤ) s.it = .ok s.rest s.p a
          ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => p it = .error e) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.dropMany1, SeqRight.seqRight, bind]
    cases hp1 : p it with
    | error e => rfl
    | ok r1 h1 x =>
      dsimp only
      obtain ⟨it', a, pr, hr, -⟩ := foldl_of_eq _ _ p (fun _ => True) trivial
        (fun _ _ _ _ => trivial) r1 (r := (ParseIt.dropMany p : Parser ε ι τ Unitᵤ) r1) rfl
      rw [hr]
      exact fun hp => Progress.advanced_of_trans pr (hp _ _ _ _ hp1))

/-- `dropManyN n p` consumes input when `n > 0` and `p` always consumes input; on failure the
error is an error of `p`. -/
@[spec] theorem Spec.dropManyN [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.dropManyN n p : Parser ε ι τ Unitᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it ∧ (ParseIt.dropManyN n p : Parser ε ι τ Unitᵤ) s.it = .ok s.rest s.p a
          ∧ (0 < n → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.dropManyN, SeqRight.seqRight, bind]
    rcases drop_of_eq n p it (r := (ParseIt.drop n p : Parser ε ι τ Unitᵤ) it) rfl with
      ⟨r1, h1, hr1, hadv1⟩ | ⟨e, hr1, he⟩
    · rw [hr1]
      dsimp only
      obtain ⟨it', a, pr, hr, -⟩ := foldl_of_eq _ _ p (fun _ => True) trivial
        (fun _ _ _ _ => trivial) r1 (r := (ParseIt.dropMany p : Parser ε ι τ Unitᵤ) r1) rfl
      rw [hr]
      exact fun hn hp => Progress.advanced_of_trans pr (hadv1 hn hp)
    · rw [hr1]
      exact he)

/-- `dropUntil stop p` returns an output of `stop`; on failure the error is an error of `p` or
of `stop`. -/
@[spec] theorem Spec.dropUntil [Iterators.Finite ι Id]
  (stop : ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.dropUntil stop p : Parser ε ι τ β)
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it ∧ (ParseIt.dropUntil stop p : Parser ε ι τ β) s.it = .ok s.rest s.p b
          ∧ (∃ it' it'' pr, stop it' = .ok it'' pr b))
        (fun e => (∃ it'', p it'' = .error e) ∨ (∃ it'', stop it'' = .error e)) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.dropUntil, Functor.map, bind, pure, Function.comp]
    rcases foldlUntil.loop_of_eq (γ := Unitᵤ) (fun _ _ => ⟨⟩) stop p it ⟨⟩ it (.refl it)
        (r := (ParseIt.foldlUntil (γ := Unitᵤ) (fun _ _ => ⟨⟩) ⟨⟩ stop p : Parser ε ι τ (Unitᵤ × β)) it)
        rfl with
      ⟨it', pr, xs, z, hr, -, hz⟩ | ⟨e, hr, he⟩
    · rw [hr]
      simpa using hz
    · rw [hr]
      exact he)

/-- `count p` never fails, and consumes input when the count is non-zero and `p` always
consumes input. -/
@[spec] theorem Spec.count [Iterators.Finite ι Id] (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.count p : Parser ε ι τ Natᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun n s => s.it = it ∧ (ParseIt.count p : Parser ε ι τ Natᵤ) s.it = .ok s.rest s.p n
          ∧ (n.val ≠ 0 → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', b, pr, hr, -, hne⟩ := foldl_of_eq _ _ p (fun _ => True) trivial
      (fun _ _ _ _ => trivial) it (r := (ParseIt.count p : Parser ε ι τ Natᵤ) it) rfl
    rw [hr]
    exact fun hv => hne (by rintro rfl; exact hv rfl))

/-- `countUpTo n p` never fails: it returns a count of at most `n`, consuming input when the
count is non-zero and `p` always consumes input. -/
@[spec] theorem Spec.countUpTo [Iterators.Finite ι Id] (n : Nat) (p : ParserT ε ι τ Id α)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.countUpTo n p : Parser ε ι τ Natᵤ)
        (fun s => s.it = it ∧ s.rest = it)
        (fun c s => s.it = it ∧ (ParseIt.countUpTo n p : Parser ε ι τ Natᵤ) s.it = .ok s.rest s.p c
          ∧ c.val ≤ n
          ∧ (c.val ≠ 0 → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    obtain ⟨it', pr, xs, hr, hlen, -, hadv⟩ :=
      foldlUpTo_of_eq n _ _ p it (r := (ParseIt.countUpTo n p : Parser ε ι τ Natᵤ) it) rfl
    rw [hr]
    have hv : (xs.foldl (fun (n : Natᵤ.{u}) (_ : α) => (⟨n.val + 1⟩ : Natᵤ.{u})) 0).val
        = xs.length := by
      rw [foldl_succ_val]; exact Nat.zero_add _
    refine ⟨by rw [hv]; exact hlen, fun hc => hadv ?_⟩
    rintro rfl
    exact hc rfl)

/-- `countUntil stop p` pairs a count with an output of `stop`; on failure the error is an error
of `p` or of `stop`. -/
@[spec] theorem Spec.countUntil [Iterators.Finite ι Id]
  (stop : ParserT ε ι τ Id β) (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.countUntil stop p : Parser ε ι τ (Natᵤ × β))
        (fun s => s.it = it ∧ s.rest = it)
        (fun b s => s.it = it
          ∧ (ParseIt.countUntil stop p : Parser ε ι τ (Natᵤ × β)) s.it = .ok s.rest s.p b
          ∧ (∃ it' it'' pr, stop it' = .ok it'' pr b.2))
        (fun e => (∃ it'', p it'' = .error e) ∨ (∃ it'', stop it'' = .error e)) :=
  Spec.of_apply _ it _ _ (by
    rcases foldlUntil.loop_of_eq _ stop p it 0 it (.refl it)
        (r := (ParseIt.countUntil stop p : Parser ε ι τ (Natᵤ × β)) it) rfl with
      ⟨it', pr, xs, z, hr, -, hz⟩ | ⟨e, hr, he⟩
    · rw [hr]
      exact hz
    · rw [hr]
      exact he)

/-- `endBy sep p strict` returns outputs of `p`, consuming input when the result is non-empty and
`p` always consumes input; it only fails when `strict`, with an error of `sep`. -/
@[spec] theorem Spec.endBy [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool) (it : Iter (α := ι) τ)
    : Triple (ParseIt.endBy sep p strict : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.endBy sep p strict : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (a ≠ #[] → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => strict = true ∧ ∃ it'', sep it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases endBy_of_eq sep p strict it
        (r := (ParseIt.endBy sep p strict : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hmem, hne⟩ | ⟨hst, e, hr, hsep⟩
    · rw [hr]
      exact ⟨hmem, hne⟩
    · rw [hr]
      exact ⟨hst, hsep⟩)

/-- `endBy1 sep p strict` returns a non-empty array of outputs of `p`, consuming input when `p`
always consumes input; on failure the error is that of the first `p <* sep` at `it` or, when
`strict`, an error of `sep`. -/
@[spec] theorem Spec.endBy1 [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool) (it : Iter (α := ι) τ)
    : Triple (ParseIt.endBy1 sep p strict : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.endBy1 sep p strict : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ 0 < a.size ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => (p <* sep : Parser ε ι τ α) it = .error e
          ∨ (strict = true ∧ ∃ it'', sep it'' = .error e)) :=
  Spec.of_apply _ it _ _ (by
    rcases endBy1_of_eq sep p strict it
        (r := (ParseIt.endBy1 sep p strict : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hpos, hmem, hadv⟩ | ⟨e, he, hr⟩ | ⟨hst, e, hr, hsep⟩
    · rw [hr]
      exact ⟨hpos, hmem, hadv⟩
    · rw [hr]
      exact .inl he
    · rw [hr]
      exact .inr ⟨hst, hsep⟩)

/-- `sepBy sep p strict` returns outputs of `p`, consuming input when the result is non-empty and
`p` always consumes input; it only fails when `strict`, with an error of `p`. -/
@[spec] theorem Spec.sepBy [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool) (it : Iter (α := ι) τ)
    : Triple (ParseIt.sepBy sep p strict : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.sepBy sep p strict : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (a ≠ #[] → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => strict = true ∧ ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases sepBy_of_eq sep p strict it
        (r := (ParseIt.sepBy sep p strict : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hmem, hne⟩ | ⟨hst, e, hr, hperr⟩
    · rw [hr]
      exact ⟨hmem, hne⟩
    · rw [hr]
      exact ⟨hst, hperr⟩)

/-- `sepBy1 sep p strict` returns a non-empty array of outputs of `p`, consuming input when `p`
always consumes input; on failure the error is that of the first `p` at `it` or, when `strict`,
an error of `p`. -/
@[spec] theorem Spec.sepBy1 [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (strict : Bool) (it : Iter (α := ι) τ)
    : Triple (ParseIt.sepBy1 sep p strict : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.sepBy1 sep p strict : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ 0 < a.size ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => p it = .error e ∨ (strict = true ∧ ∃ it'', p it'' = .error e)) :=
  Spec.of_apply _ it _ _ (by
    rcases sepBy1_of_eq sep p strict it
        (r := (ParseIt.sepBy1 sep p strict : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hpos, hmem, hne⟩ | ⟨e, he, hr⟩ | ⟨hst, e, hr, hperr⟩
    · rw [hr]
      exact ⟨hpos, hmem, hne (Array.ne_empty_of_size_pos hpos)⟩
    · rw [hr]
      exact .inl he
    · rw [hr]
      exact .inr ⟨hst, hperr⟩)

/-- `sepNoEndBy sep p` returns outputs of `p`, consuming input when the result is non-empty and
`p` always consumes input; on failure the error is an error of `p`. -/
@[spec] theorem Spec.sepNoEndBy [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.sepNoEndBy sep p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.sepNoEndBy sep p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (a ≠ #[] → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases sepBy_of_eq sep p true it
        (r := (ParseIt.sepNoEndBy sep p : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hmem, hne⟩ | ⟨-, e, hr, hperr⟩
    · rw [hr]
      exact ⟨hmem, hne⟩
    · rw [hr]
      exact hperr)

/-- `sepNoEndBy1 sep p` returns a non-empty array of outputs of `p`, consuming input when `p`
always consumes input; on failure the error is an error of `p`. -/
@[spec] theorem Spec.sepNoEndBy1 [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.sepNoEndBy1 sep p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.sepNoEndBy1 sep p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ 0 < a.size ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => ∃ it'', p it'' = .error e) :=
  Spec.of_apply _ it _ _ (by
    rcases sepBy1_of_eq sep p true it
        (r := (ParseIt.sepNoEndBy1 sep p : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hpos, hmem, hne⟩ | ⟨e, he, hr⟩ | ⟨-, e, hr, hperr⟩
    · rw [hr]
      exact ⟨hpos, hmem, hne (Array.ne_empty_of_size_pos hpos)⟩
    · rw [hr]
      exact ⟨it, he⟩
    · rw [hr]
      exact hperr)

/-- `sepEndBy sep p` never fails: it returns outputs of `p`, consuming input when the result is
non-empty and `p` always consumes input. -/
@[spec] theorem Spec.sepEndBy [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.sepEndBy sep p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.sepEndBy sep p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ (a ≠ #[] → (∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun _ => False) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.sepEndBy, SeqLeft.seqLeft, bind, pure]
    rcases sepBy_of_eq sep p false it
        (r := (ParseIt.sepBy sep p false : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hmem, hne⟩ | ⟨hst, -⟩
    · rw [hr]
      dsimp only
      obtain ⟨r2, pr2, ho⟩ := optional_of_eq (sep : Parser ε ι τ β) it'
        (r := (ParseIt.optional sep : Parser ε ι τ Unitᵤ) it') rfl
      rw [ho]
      exact ⟨hmem, fun h hp => Progress.advanced_of_trans pr2 (hne h hp)⟩
    · cases hst)

/-- `sepEndBy1 sep p` returns a non-empty array of outputs of `p`, consuming input when `p`
always consumes input; on failure the error is that of the first `p` at `it`. -/
@[spec] theorem Spec.sepEndBy1 [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
  (p : ParserT ε ι τ Id α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.sepEndBy1 sep p : Parser ε ι τ (Array α))
        (fun s => s.it = it ∧ s.rest = it)
        (fun a s => s.it = it
          ∧ (ParseIt.sepEndBy1 sep p : Parser ε ι τ (Array α)) s.it = .ok s.rest s.p a
          ∧ 0 < a.size ∧ (∀ x ∈ a, ∃ it' it'' pr, p it' = .ok it'' pr x)
          ∧ ((∀ s rest (h : Progress rest s) x, p s = .ok rest h x → Advanced rest s)
              → Advanced s.rest it))
        (fun e => p it = .error e) :=
  Spec.of_apply _ it _ _ (by
    simp only [ParseIt.sepEndBy1, SeqLeft.seqLeft, bind, pure]
    rcases sepBy1_of_eq sep p false it
        (r := (ParseIt.sepBy1 sep p false : Parser ε ι τ (Array α)) it) rfl with
      ⟨it', a, pr, hr, hpos, hmem, hne⟩ | ⟨e, he, hr⟩ | ⟨hst, -⟩
    · rw [hr]
      dsimp only
      obtain ⟨r2, pr2, ho⟩ := optional_of_eq (sep : Parser ε ι τ β) it'
        (r := (ParseIt.optional sep : Parser ε ι τ Unitᵤ) it') rfl
      rw [ho]
      exact ⟨hpos, hmem, fun hp => Progress.advanced_of_trans pr2
        (hne (Array.ne_empty_of_size_pos hpos) hp)⟩
    · rw [hr]
      exact he
    · cases hst)
