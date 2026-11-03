module

public import Init.Meta
public import Std.WP

public import ParseIt
import all ParseIt.Basic

import Std.Tactic.Do

open Std Std.WP Lean ParseIt

@[expose] public section

namespace ParseIt

/-! WP instances for ParseIt.Parser -/

variable {ε ι τ α : Type u} [Iterator ι Id τ]

/-- `Progress.refl` is the `stay` constructor. -/
@[simp] theorem Progress.refl_eq {it : Iter (α := ι) τ}
    : Progress.refl it = .stay rfl  := by
  rfl

/-- `Progress.stay rfl` is a left identity for `Progress.trans`. -/
@[simp, grind .] theorem Progress.refl_trans' {it' it : Iter (α := ι) τ} (h : Progress it' it) :
    (Progress.stay rfl : Progress it' it').trans h = h := by
  cases h <;> rfl

/-- `Progress.stay rfl` is a right identity for `Progress.trans`. -/
@[simp, grind .] theorem Progress.trans_refl' {it' it : Iter (α := ι) τ} (h : Progress it' it) :
    h.trans (Progress.stay rfl : Progress it it) = h := by
  cases h <;> rfl

/-- `Progress.trans` is associative. -/
@[simp, grind .] theorem Progress.trans_assoc' {it''' it'' it' it : Iter (α := ι) τ}
    (h₁ : Progress it''' it'') (h₂ : Progress it'' it') (h₃ : Progress it' it) :
    (h₁.trans h₂).trans h₃ = h₁.trans (h₂.trans h₃) := by
  cases h₁ <;> cases h₂ <;> cases h₃ <;> rfl

/-- `Parser ε ι τ` is a lawful monad. -/
instance : LawfulMonad (Parser ε ι τ) where
  id_map := by
    intros
    simp [Functor.map, Function.comp, bind, pure, Progress.trans]
    apply funext
    grind
  map_const := by intros; rfl
  seqLeft_eq := by
    intro _ _ x y; funext it
    simp only [Functor.map, SeqLeft.seqLeft, Seq.seq, bind, pure, Function.comp]
    cases x it <;> simp only [] <;> cases y _ <;>
      simp [Progress.refl, Progress.refl_trans']
  seqRight_eq := by
    intro _ _ x y; funext it
    simp only [Functor.map, SeqRight.seqRight, Seq.seq, bind, pure, Function.comp]
    cases x it <;> simp only [] <;> cases y _ <;>
      simp [Progress.refl, Progress.refl_trans']
  pure_seq := by
    intro _ _ g x; funext it
    simp only [Functor.map, Seq.seq, bind, pure, Function.comp]
    cases x it <;> simp
  bind_pure_comp := by solve_by_elim
  bind_map := by
    intros
    simp [Seq.seq, bind, pure, Functor.map]
    apply funext
    intros
    grind
  pure_bind := by
    intro _ _ x f; funext it
    simp only [bind, pure]
    cases f x it <;> simp
  bind_assoc := by
    intro _ _ _ x f g; funext it
    simp only [bind]
    cases x it with
    | error => rfl
    | ok rest h a =>
      dsimp only [pure]
      cases f a rest with
      | error => rfl
      | ok rest' h' b =>
        dsimp only [pure]
        cases g b rest' with
        | error => rfl
        | ok rest'' h'' c => simp

/-- The postcondition for a ParseIt.Result -/
def pushResult (it : Iter (α := ι) τ)
  (post : α → (it' : Iter (α := ι) τ) → Progress it' it → Prop) (epost : ε → Prop)
    : (ParseIt.Result ε it α) → Prop
  | .ok s h a => post a s h
  | .error el => epost el

/-- `pushResult` on a successful result applies the success postcondition. -/
@[simp, grind =] theorem pushResult_ok (it : Iter (α := ι) τ)
  (post : α → (it' : Iter (α := ι) τ) → Progress it' it → Prop) (epost : ε → Prop)
  (s : Iter (α := ι) τ) (h : Progress s it) (a : α)
    : pushResult it post epost (.ok s h a) = post a s h := rfl

/-- `pushResult` on an error applies the error postcondition. -/
@[simp, grind =] theorem pushResult_error (it : Iter (α := ι) τ)
  (post : α → (it' : Iter (α := ι) τ) → Progress it' it → Prop) (epost : ε → Prop)
  (e : ε) : pushResult it post epost (.error e) = epost e := rfl

/-- Weakest-precondition interpretation of a function producing a `ParseIt.Result` from an iterator
and a progress proof. -/
instance Result.instWP (it : Iter (α := ι) τ)
    : WP ((it' : Iter (α := ι) τ) → Progress it' it → ParseIt.Result ε it α) α
      ((it' : Iter (α := ι) τ) → Progress it' it → Prop) (ε → Prop)  where
  wpTrans x := ⟨fun post epost s h => pushResult it post epost (x s h)⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s h => by
    cases hxs : x s h with
    | ok s' h' a => simpa [hxs] using hpost a s' h'
    | error el => simpa [hxs] using hepost el

/-- Parser state used in specifications: the iterator `it` where parsing started, the current
iterator `rest`, and a proof that `rest` was reached from `it`. -/
@[ext] structure IterWithProgress (ι τ : Type u) [Iterator ι Id τ] where
  /-- The iterator where parsing started. -/
  it : Iter (α := ι) τ
  /-- The current iterator (remaining input). -/
  rest : Iter (α := ι) τ
  /-- Proof that `rest` was reached from `it`. -/
  p : Progress rest it

/-- Extend the state `it` by further progress from `it.rest` to `rest`, keeping the start iterator. -/
def IterWithProgress.trans (it : IterWithProgress ι τ) (rest : Iter (α := ι) τ) (h : Progress rest it.rest) :=
  IterWithProgress.mk it.it rest (h.trans it.p)

/-- The state at `it` where no input has been consumed yet. -/
def IterWithProgress.refl (it : Iter (α := ι) τ) :=
  IterWithProgress.mk it it (.refl it)

/-- Weakest-precondition interpretation of `Parser`: run the parser from the current iterator
`it.rest` and check the postcondition on the extended `IterWithProgress` state, or the error
postcondition on failure. -/
instance Parser.instWP
    : WP (Parser ε ι τ α) α (IterWithProgress ι τ → Prop) (ε → Prop)  where
  wpTrans x := ⟨fun post epost it => pushResult it.rest
                (fun a it' h' => post a (IterWithProgress.mk it.it it' (h'.trans it.p)))
                epost (Parser.run x it.rest)⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    grind only [= pushResult.eq_def]

/-- Extract the concrete behaviour of `x it` from a Hoare triple whose precondition holds at the
initial state `IterWithProgress.refl it`. -/
theorem Parser.of_wp_eq
  (x : Parser ε ι τ α) (h : Triple x pre post epost) (it : Iter (α := ι) τ)
  (hp : pre (IterWithProgress.refl it))
    : match x it with | .ok s h a => post a (IterWithProgress.mk it s h) | .error e => epost e := by
  have := Triple.iff.mp h
  simp only [Order.PartialOrder.rel, wp, WP.trans, pushResult, Parser.run] at this
  have := this (IterWithProgress.mk it it (.refl it)) (by grind [IterWithProgress.refl])
  split at this <;> simp_all

/-- `Parser` is a `WPMonad`: its weakest-precondition interpretation respects `pure` and `bind`. -/
instance Parser.instWPMonad
    : WPMonad (Parser ε ι τ) ((it : IterWithProgress ι τ) → Prop) (ε → Prop) where
  toWP α := @Parser.instWP ε ι τ _ _
  pure_le_wp_pure x := fun post epost _ => by
    simp [pure, wp, WP.trans, Parser.run]
  bind_le_wp_bind x f := fun post epost it => by
    simp only [wp, WP.trans, bind, Parser.run, pushResult, pure, Order.PartialOrder.rel]
    grind
