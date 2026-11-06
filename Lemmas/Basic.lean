module

public import Init.Meta

import all ParseIt.Error
import all ParseIt.Basic
public import ParseIt

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax
public import Std.WP

public import Lemmas.Instances

open Std Std.WP Lean ParseIt ParseIt.Char

@[expose] public section

set_option experimental.vcgen true

namespace ParseIt

/-! Theorems for ParseIt.Basic -/

variable {ε ι τ α β : Type u} [Iterator ι Id τ]

/-- `Advanced` is irreflexive for finite iterators: an iterator never strictly advances past itself. -/
@[simp, grind .] theorem Advanced.irrefl [Iterators.Finite ι Id] (it : Iter (α := ι) τ)
    : ¬ Advanced it it := by
  have key : ∀ a, Acc (IterM.TerminationMeasures.Finite.Rel (α := ι) (m := Id)) a →
      ¬ IterM.TerminationMeasures.Finite.Rel a a :=
    fun a ha => ha.rec (fun x _ ih hx => ih x hx hx)
  exact key _ ((inferInstance : WellFoundedRelation (IterM.TerminationMeasures.Finite ι Id)).wf.apply _)

/-- For finite iterators, the only `Progress` proof from an iterator to itself is `Progress.refl`. -/
theorem Progress.eq_refl [Iterators.Finite ι Id] {it : Iter (α := ι) τ} (p : Progress it it) :
    p = Progress.refl it := by
  cases p with
  | stay => rfl
  | moved h => exact absurd h (Advanced.irrefl it)

/-- For finite iterators, composing a `Progress` proof with a self-progress is a no-op. -/
theorem Progress.trans_self [Iterators.Finite ι Id] {it' it : Iter (α := ι) τ}
  (h : Progress it' it) (h' : Progress it it) : h.trans h' = h := by
  rw [Progress.eq_refl h', Progress.refl_eq, Progress.trans_refl']

/-- A spec for `x` started at the parse start `it` also holds when `x` is started at `it` with an
arbitrary parse start `it₀`, as long as the postcondition only depends on the current iterator. -/
theorem Spec.from_start {x : Parser ε ι τ α} {Q : α → Iter (α := ι) τ → Prop}
  {E : ε → Prop} (it₀ it : Iter (α := ι) τ)
  (h : Triple x (fun s => s.it = it ∧ s.rest = it) (fun a s => s.it = it ∧ Q a s.rest) E)
    : Triple x (fun s => s.it = it₀ ∧ s.rest = it) (fun a s => s.it = it₀ ∧ Q a s.rest) E :=
   Triple.intro (by
    have := Parser.of_wp_eq _ h it (by simp [IterWithProgress.refl])
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl⟩
    revert this
    generalize x s.rest = r
    cases r <;> simp_all)

/-- Any `x` started at `it` (with parse start `it₀`) never moves backwards from `it`. -/
theorem Spec.progress
  (x : Parser ε ι τ α) (it₀ it : Iter (α := ι) τ)
    : Triple x
      (fun s => s.it = it₀ ∧ s.rest = it)
      (fun _ s => s.it = it₀ ∧ (s.rest = it ∨ Advanced s.rest it))
      (fun _ => True) :=
  Triple.intro (by
    rintro ⟨s⟩ ⟨h1, rfl⟩
    simp only [wp, WP.trans, pushResult]
    split
    next _ _ hp _ _ =>
      refine ⟨h1, ?_⟩
      cases hp with
      | stay h => exact .inl h
      | moved h => exact .inr h
    · trivial)

/-- Generic specification of an arbitrary parser `x` started at `it`: on success the final state is
exactly what `x it` returns, and on failure the error is the one `x it` returns. -/
theorem Spec.default_parser [Iterators.Finite ι Id]
  (x : Parser ε ι τ α) (it : Iter (α := ι) τ)
    : Triple x
      (fun s => s.it = it ∧ s.rest = it)
      (fun a s => s.it = it ∧ x s.it = .ok s.rest s.p a)
      (fun e => x it = .error e) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, wp, WP.trans, Parser.run, pushResult]
    rintro ⟨it, rest, p⟩ ⟨h₁, h₂⟩
    dsimp only at h₁ h₂ ⊢
    subst it rest
    rw [Progress.eq_refl p]
    cases x it <;> simp [Progress.refl])

/-- `pure default` succeeds without consuming input and returns `default`. -/
@[spec] theorem Spec.pure_parser [inst : Inhabited α] (it : Iter (α := ι) τ)
    : Triple (pure inst.default : Parser ε ι τ α)
      (fun s => s.it = it ∧ s.rest = it)
      (fun a s => s.it = it ∧ s.rest = it ∧ a  = inst.default)
      (fun _ => False) := by
  vcgen with finish

/-- Lifting a pure `Id` value into `ParserT` succeeds without consuming input and returns that value. -/
@[spec] theorem Spec.monadLift (default : α) (it : Iter (α := ι) τ)
    : Triple (MonadLift.monadLift (@monadLift Id Id (instMonadLiftT Id) α default : Id α) : ParserT ε ι τ Id α)
      (fun s => s.it = it ∧ s.rest = it)
      (fun (a : α) (s : IterWithProgress ι τ) => it = s.it ∧ s.rest = it ∧ a = default)
      (fun _ => False) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run, pushResult,
                MonadLift.monadLift, MonadLiftT.monadLift, bind, pure]
    simp_all)

/-- `p <|> q` (starting with no input consumed): if `p` succeeds at the current position its result is
used, otherwise `q` is run from the same position. -/
@[spec] theorem Spec.orElse_Parser
  (p : Parser ε ι τ α) (q : Parser ε ι τ α)
  (post : α → (it : IterWithProgress ι τ) → Prop) (epost : ε → Prop)
    : Triple (p <|> q)
      (fun (s : IterWithProgress ι τ) =>
          s.it = s.rest ∧
          match p s.rest with
          | .ok s' h' a => post a (s.trans s' h')
          | .error _ => wp q post epost s) post epost :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run, HOrElse.hOrElse, OrElse.orElse,
      MonadExcept.orElse, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, IterWithProgress.trans]
    intro s
    cases p s.rest <;> simp [bind, pure])

/-- `p *> q` satisfies `post` whenever running `p` and then `q` does; the result of `p` is discarded. -/
@[spec] theorem Spec.seqRigth_Parser
  (p : Parser ε ι τ α) (q : Parser ε ι τ β)
  (post : β → (it : IterWithProgress ι τ) → Prop) (epost : ε → Prop)
    : Triple (p *> q)
      (fun s => wp p (fun _ s => wp q post epost s) epost s) post epost :=
  Triple.intro (by
    simp [WP.wp, WP.trans, SeqRight.seqRight, pushResult, Parser.run, bind, pure]
    intro s
    grind only [Progress.trans_assoc'])

/-- Evaluation of `x *> pure default`: run `x` and replace its result by `default`. -/
@[simp, grind .] theorem seqRight_pure_apply [inst : Inhabited β] (x : Parser ε ι τ α) (it : Iter (α := ι) τ) :
    (x *> pure inst.default : Parser ε ι τ β) it =
      match x it with
      | .ok rest h _ => .ok rest h inst.default
      | .error e => .error e := by
  simp only [SeqRight.seqRight, bind, pure]
  cases x it <;> simp

/-- `p <* q` runs `p` and then `q` from where `p` stopped, returning the result of `p`; an error of
either parser is propagated. -/
@[spec] theorem Spec.seqLeft_Parser
  (p : Parser ε ι τ α) (q : Parser ε ι τ β)
  (post : α → (it : IterWithProgress ι τ) → Prop) (epost : ε → Prop)
    : Triple (p <* q)
      (fun s => wp p (fun a (s : IterWithProgress ι τ) =>
          match q s.rest with | .ok s' h' _ => post a (IterWithProgress.mk s.it s' (h'.trans s.p)) | .error e => epost e)
          epost s) post epost :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, SeqLeft.seqLeft, pushResult, Parser.run,
      bind, pure]
    intro s
    generalize p s.rest = r
    cases r with
    | error => exact id
    | ok rest h a =>
      dsimp only
      generalize q rest = r'
      cases r' with
      | error => exact id
      | ok rest' h' b => simp [Progress.trans_assoc'])

/-- Evaluation of `pure default <* x`: run `x` and return `default` instead of its result. -/
@[simp] theorem seqLeft_pure_apply [inst : Inhabited α] (x : Parser ε ι τ β) (it : Iter (α := ι) τ) :
    (pure inst.default <* x : Parser ε ι τ α) it =
      match x it with
      | .ok rest h _ => .ok rest h inst.default
      | .error e => .error e := by
  simp only [SeqLeft.seqLeft, bind, pure]
  cases x it <;> simp

/-- `withSpan x` behaves like `x` and additionally returns the positions of the start iterator `it`
and of the iterator after `x`. -/
@[spec] theorem Spec.withSpan [HasPos ι τ]
  (x : Parser ε ι τ α) (h : Triple x pre post epost) (it : Iter (α := ι) τ)
    : Triple (ParseIt.withSpan x : Parser ε ι τ (α × HasPos.Pos ι × HasPos.Pos ι))
      (fun s => s.it = it ∧ s.rest = it ∧ pre s)
      (fun (a : (α × HasPos.Pos ι × HasPos.Pos ι)) s => s.it = it ∧
        post a.1 s ∧ a.2.1 = HasPos.pos it ∧ a.2.2 = HasPos.pos s.rest) epost :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl, hpre⟩
    have := Triple.iff.mp h s hpre
    simp only [WP.wp, WP.trans, Parser.run] at this
    simp only [ParseIt.withSpan, bind, pure]
    revert this
    generalize x s.rest = r
    cases r <;> simp [hit])

/-- `throwUnexpected input` always fails with `Error.unexpected it input`. -/
@[spec] theorem Spec.throwUnexpected [Error ε ι τ]
  (input : Option τ) (it : Iter (α := ι) τ)
    : Triple (throwUnexpected input : Parser ε ι τ α)
      (fun s => s.rest = it)  (fun _ _ => False) (fun e => e = Error.unexpected it input) :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s rfl
    simp [ParseIt.throwUnexpected, pure])

/-- `throwUnexpectedWithMessage input msg` always fails with `Error.unexpected it input` annotated
with `msg`. -/
@[spec] theorem Spec.throwUnexpectedWithMessage [Error ε ι τ]
  (input : Option τ) (msg : String) (it : Iter (α := ι) τ)
    : Triple (throwUnexpectedWithMessage input msg : Parser ε ι τ α)
      (fun s => s.rest = it) (fun _ _ => False) (fun e => e = Error.addMessage (Error.unexpected it input) it msg) :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s rfl
    simp [ParseIt.throwUnexpectedWithMessage, pure])

/-- Evaluation of `throwUnexpectedWithMessage input msg` at `it`. -/
@[simp, grind .] theorem throwUnexpectedWithMessage_eq_error [Error ε ι τ]
  (input : Option τ) (msg : String) (it : Iter (α := ι) τ)
    : (throwUnexpectedWithMessage input msg : Parser ε ι τ α) it =
      .error (Error.addMessage (Error.unexpected it input) it msg) := by
  rfl

/-- `withErrorMessage msg x` behaves like `x` on success; on failure the error `e'` of `x` is
annotated with `msg` at position `it`. -/
@[spec] theorem Spec.withErrorMessage [Iterators.Finite ι Id] [Error ε ι τ]
  (x : Parser ε ι τ α) (h : Triple x pre post epost) (msg : String) (it : Iter (α := ι) τ)
    : Triple (withErrorMessage msg x : Parser ε ι τ α)
      (fun s => s.it = it ∧ s.rest = it ∧ pre s)
      (fun a s => post a s ∧ s.it = it ∧ ParseIt.withErrorMessage msg x s.it = .ok s.rest s.p a)
      (fun e => ∃ e', epost e' ∧ e = Error.addMessage e' it msg) :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro ⟨it₀, rest, p⟩ ⟨h₁, h₂, hpre⟩
    dsimp only at h₁ h₂
    subst it₀ rest
    have := Triple.iff.mp h _ hpre
    simp only [WP.wp, WP.trans, Parser.run] at this ⊢
    rw [Progress.eq_refl p] at this ⊢
    simp only [ParseIt.withErrorMessage, bind, pure]
    revert this
    generalize x it = r
    cases r with
    | ok => simp [Progress.refl]
    | error e => simpa using fun he => ⟨e, he, rfl⟩)

/-- `lookAhead x` runs `x` without consuming input: on success the result of `x` is returned and the
position is reset to `it`. -/
@[spec] theorem Spec.lookAhead
  (x : Parser ε ι τ α) (h : Triple x pre post epost) (it : Iter (α := ι) τ)
    : Triple (ParseIt.lookAhead x)
      (fun s => s.it = it ∧ s.rest = it ∧ pre s)
      (fun a s => s.it = it ∧ s.rest = it ∧ ∃ rest h, post a (IterWithProgress.mk s.it rest h)) epost :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl, hpre⟩
    have := Triple.iff.mp h s hpre
    simp only [WP.wp, WP.trans, Parser.run] at this
    simp only [ParseIt.lookAhead, bind, pure]
    revert this
    generalize x s.rest = r
    cases r with
    | ok rest h' a => simpa [hit] using fun hpost => ⟨rest, _, hpost⟩
    | error => simp)

/-- `notFollowedBy x` succeeds without consuming input exactly when `x` fails at `it`; otherwise it
fails with `Error.unexpected it none`. -/
@[spec] theorem Spec.notFollowedBy [Error ε ι τ]
  (x : Parser ε ι τ α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.notFollowedBy x : Parser ε ι τ Unitᵤ)
      (fun s => s.it = it ∧ s.rest = it)
      (fun _ s => s.it = it ∧ s.rest = it ∧ ∃ e, x it = .error e)
      (fun e => e = (Error.unexpected it none) ∧ ∃ rest h a, x it = .ok rest h a) :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl⟩
    simp only [ParseIt.notFollowedBy, bind, pure]
    cases x s.rest with
    | ok rest h a => simpa using ⟨rest, h, a, rfl⟩
    | error e => simpa [hit] using ⟨e, rfl⟩)

/-- `eoption x` never fails: it returns `.inl v` (after the input consumed by `x`) if `x` succeeds
with `v`, and `.inr e` without consuming input if `x` fails with `e`. -/
@[spec] theorem Spec.eoption (x : Parser ε ι τ α)  (it : Iter (α := ι) τ)
    : Triple (ParseIt.eoption x : Parser ε ι τ (Sum α ε))
      (fun s => s.it = it ∧ s.rest = it)
      (fun (a : Sum α ε) (s : IterWithProgress ι τ) =>
          match x it with
          | .ok rest _ v =>  s.it = it ∧ s.rest = rest ∧ a = .inl v
          | .error e => s.it = it ∧ s.rest = it ∧ a = .inr e)
      (fun _ => False) :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl⟩
    simp only [ParseIt.eoption, bind, pure]
    cases x s.rest <;> simp [hit])

/-- `optionD x default` never fails: it returns the result of `x` if `x` succeeds, and `default`
without consuming input otherwise. -/
@[spec] theorem Spec.optionD (x : Parser ε ι τ α) (default : α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.optionD x default : Parser ε ι τ α)
      (fun s => s.it = it ∧ s.rest = it)
      (fun (a : α) (s : IterWithProgress ι τ) =>
          match x it with
          | .ok rest _ v => s.it = it ∧ s.rest = rest ∧ a = v
          | .error _ => s.it = it ∧ s.rest = it ∧ a = default)
      (fun _ => False) := by
  vcgen [ParseIt.optionD] with try finish

/-- `option! x` never fails: it returns the result of `x` if `x` succeeds, and the `Inhabited`
default without consuming input otherwise. -/
@[spec] theorem Spec.option! [inst : Inhabited α] (x : Parser ε ι τ α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.option! x : Parser ε ι τ α)
      (fun s => s.it = it ∧ s.rest = it)
      (fun (a : α) (s : IterWithProgress ι τ) =>
          match x it with
          | .ok rest _ v => s.it = it ∧ s.rest = rest ∧ a = v
          | .error _ => s.it = it ∧ s.rest = it ∧ a = inst.default)
      (fun _ => False) := by
  vcgen [ParseIt.option!] with try finish
  rename_i hpre _ _ hpost
  obtain ⟨rfl, -⟩ := hpre
  exact hpost

/-- `option? x` never fails: it returns `some v` if `x` succeeds with `v`, and `none` without
consuming input otherwise. -/
@[spec] theorem Spec.option? (x : Parser ε ι τ α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.option? x : Parser ε ι τ (Option α))
      (fun s => s.it = it ∧ s.rest = it)
      (fun (a : Option α) (s : IterWithProgress ι τ) =>
          match x it with
          | .ok rest _ v => s.it = it ∧ s.rest = rest ∧ a = some v
          | .error _ => s.it = it ∧ s.rest = it ∧ a = none)
      (fun _ => False) := by
  vcgen [ParseIt.option?] with try finish
  rename_i hpre _ _ hpost
  obtain ⟨rfl, -⟩ := hpre
  revert hpost
  simp only [Functor.map, bind, pure]
  cases x _ <;> simp [Function.comp]

/-- `optional x` never fails: it consumes what `x` consumes if `x` succeeds, and nothing otherwise. -/
@[spec] theorem Spec.optional (x : Parser ε ι τ α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.optional x : Parser ε ι τ Unitᵤ)
      (fun s => s.it = it ∧ s.rest = it)
      (fun (_ : Unitᵤ) (s : IterWithProgress ι τ) =>
          match x it with
          | .ok rest _ _ => s.it = it ∧ s.rest = rest
          | .error _ => s.it = it ∧ s.rest = it)
      (fun _ => False) := by
  vcgen [ParseIt.optional] with finish
