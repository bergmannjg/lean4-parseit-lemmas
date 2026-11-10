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
public theorem foldlP_of_eq [Iterators.Finite ι Id]
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

public theorem endBy_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
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
public theorem endBy1_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
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

public theorem sepBy_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
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

public theorem sepBy1_of_eq [Iterators.Finite ι Id] (sep : ParserT ε ι τ Id β)
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
public theorem tokenMap_of_eq [Iterators.Productive ι Id] [Error ε ι τ] (f : τ → Option α)
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
