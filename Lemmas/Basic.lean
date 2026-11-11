module

public import Init.Meta

import all ParseIt.Error
import all ParseIt.Basic

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

/-- For finite iterators, the only `Progress` proof from an iterator to itself is `Progress.refl`. -/
theorem Progress.eq_refl [Iterators.Finite ι Id] {it : Iter (α := ι) τ} (p : Progress it it) :
    p = Progress.refl it := by
  cases p with
  | stay => rfl
  | moved h => exact absurd h (Advanced.irrefl it)

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

/-- Evaluation of `getPos` at `it`: succeed without consuming input and return the position of `it`. -/
@[simp, grind .] theorem getPos_apply [HasPos ι τ] (it : Iter (α := ι) τ)
    : (getPos : Parser ε ι τ (HasPos.Pos ι)) it = .ok it (.refl it) (HasPos.pos it) := by
  rfl

/-- `getPos` never fails: it succeeds without consuming input and returns the position of the
current iterator `it`. -/
@[spec] theorem Spec.getPos [HasPos ι τ] (it : Iter (α := ι) τ)
    : Triple (getPos : Parser ε ι τ (HasPos.Pos ι))
      (fun s => s.it = it ∧ s.rest = it)
      (fun a s => s.it = it ∧ s.rest = it ∧ a = HasPos.pos it)
      (fun _ => False) :=
   Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro s ⟨hit, rfl⟩
    simp [hit])

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

/-- `optionD x default` never fails: it returns the result of `x` if `x` succeeds, and `default`
without consuming input otherwise. -/
public theorem optionD_of_eq
  (x : Parser ε ι τ α) (default : α) (it : Iter (α := ι) τ) {r}
  (h : (ParseIt.optionD x default : Parser ε ι τ α) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : α) (p : Progress it' it), r = .ok it' p a ∧ x it = .ok it' p a)
      ∨ (∃ e : ε, r = .ok it (.refl it) default ∧ x it = .error e) := by
  subst h
  simp only [ParseIt.optionD, ParseIt.eoption, bind, pure]
  cases x it with
  | ok rest p a => exact .inl ⟨rest, a, p, by
      have : Progress.refl rest = .stay rfl := rfl
      have : (Progress.stay rfl : Progress rest rest).trans p = p := by cases p <;> rfl
      simp [*], rfl⟩
  | error e => exact .inr ⟨e, rfl, rfl⟩

/-- `optionD x default` never fails: it returns the result of `x` if `x` succeeds, and `default`
without consuming input otherwise. -/
@[spec] theorem Spec.optionD (x : Parser ε ι τ α) (default : α) (it : Iter (α := ι) τ)
    : Triple (ParseIt.optionD x default : Parser ε ι τ α)
      (fun s => s.it = it ∧ s.rest = it)
      (fun (a : α) (s : IterWithProgress ι τ) =>
          match x it with
          | .ok rest _ v => s.it = it ∧ s.rest = rest ∧ a = v
          | .error _ => s.it = it ∧ s.rest = it ∧ a = default)
      (fun _ => False) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro ⟨sit, srest, sp⟩ ⟨hit, hrest⟩
    dsimp only at hit hrest ⊢
    subst hit hrest
    generalize hr : (ParseIt.optionD x default : Parser ε ι τ α) srest = r
    rcases optionD_of_eq x default srest hr with ⟨it', a, p, rfl, hx⟩ | ⟨e, rfl, hx⟩ <;>
      simp [pushResult, hx])

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
public theorem option?_of_eq
  (x : Parser ε ι τ α) (it : Iter (α := ι) τ) {r}
  (h : (ParseIt.option? x : Parser ε ι τ (Option α)) it = r)
    : (∃ (it' : Iter (α := ι) τ) (a : α) (p : Progress it' it), r = .ok it' p (some a) ∧ x it = .ok it' p a)
      ∨ (∃ e : ε, r = .ok it (.refl it) none ∧ x it = .error e) := by
  rcases optionD_of_eq (some <$> x) none it h with ⟨it', a, p, hr, hx⟩ | ⟨e, hr, hx⟩
  · simp only [Functor.map, bind, pure] at hx
    split at hx <;> cases hx
    rename_i a' p' hxa
    have : (Progress.refl it').trans p' = p' := by cases p' <;> rfl
    exact .inl ⟨it', a', p', by rw [hr, this], hxa⟩
  · simp only [Functor.map, bind, pure] at hx
    split at hx <;> cases hx
    exact .inr ⟨_, hr, by assumption⟩

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

/-- `first.loop combine ps e` tries the parsers of `ps` in order at `it`, starting with the error `e`
of earlier alternatives: it returns the result of the first parser that succeeds, and when all fail
it returns `e` combined with their errors from left to right. -/
private theorem first.loop_of_eq (combine : ε → ε → ε)
  (ps : List (Parser ε ι τ α)) (e : ε) (it : Iter (α := ι) τ) {r}
  (h : (ParseIt.first.loop combine ps e it : Result ε it α) = r)
    : (∃ (pre post : List (Parser ε ι τ α)) (q : Parser ε ι τ α) (rest : Iter (α := ι) τ)
          (p : Progress rest it) (a : α),
          ps = pre ++ q :: post ∧ (∀ q' ∈ pre, ∃ e', q' it = .error e') ∧
          q it = .ok rest p a ∧ r = .ok rest p a)
      ∨ (∃ es : List ε,
          ps.map (fun q => q it) = es.map (fun e' => (.error e' : Result ε it α)) ∧
          r = .error (es.foldl combine e)) := by
  subst h
  induction ps generalizing e with
  | nil => exact .inr ⟨[], rfl, rfl⟩
  | cons q ps ih =>
    simp only [ParseIt.first.loop, bind, pure]
    cases hq : q it with
    | ok rest p a => exact .inl ⟨[], ps, q, rest, p, a, rfl, by simp, hq, rfl⟩
    | error f =>
      rcases ih (combine e f) with ⟨pre, post, q', rest, p, a, hps, hpre, hq', hr⟩ | ⟨es, hes, hr⟩
      · refine .inl ⟨q :: pre, post, q', rest, p, a, by simp [hps], ?_, hq', hr⟩
        exact List.forall_mem_cons.mpr ⟨⟨_, hq⟩, hpre⟩
      · exact .inr ⟨f :: es, by simp [hq, hes], hr⟩

/-- `first ps combine` at `it` returns the result of the first parser of `ps` that succeeds at `it`.
When all parsers fail, their errors are folded with `combine` from left to right; when `ps` is
empty, it fails with `Error.unexpected it none`. -/
private theorem first_of_eq [Error ε ι τ] (ps : List (Parser ε ι τ α)) (combine : ε → ε → ε)
  (it : Iter (α := ι) τ) {r}
  (h : (ParseIt.first ps combine : Parser ε ι τ α) it = r)
    : (∃ (pre post : List (Parser ε ι τ α)) (q : Parser ε ι τ α) (rest : Iter (α := ι) τ)
          (p : Progress rest it) (a : α),
          ps = pre ++ q :: post ∧ (∀ q' ∈ pre, ∃ e', q' it = .error e') ∧
          q it = .ok rest p a ∧ r = .ok rest p a)
      ∨ (ps = [] ∧ r = .error (Error.unexpected it none))
      ∨ (∃ (e : ε) (es : List ε),
          ps.map (fun q => q it) = (e :: es).map (fun e' => (.error e' : Result ε it α)) ∧
          r = .error (es.foldl combine e)) := by
  subst h
  cases ps with
  | nil => exact .inr (.inl ⟨rfl, rfl⟩)
  | cons q ps =>
    simp only [ParseIt.first, bind, pure]
    cases hq : q it with
    | ok rest p a => exact .inl ⟨[], ps, q, rest, p, a, rfl, by simp, hq, rfl⟩
    | error e =>
      rcases first.loop_of_eq combine ps e it rfl with
        ⟨pre, post, q', rest, p, a, hps, hpre, hq', hr⟩ | ⟨es, hes, hr⟩
      · refine .inl ⟨q :: pre, post, q', rest, p, a, by simp [hps], ?_, hq', hr⟩
        exact List.forall_mem_cons.mpr ⟨⟨_, hq⟩, hpre⟩
      · exact .inr (.inr ⟨e, es, by simp [hq, hes], hr⟩)

/-- `first ps combine` started at `it` succeeds exactly like the first parser of `ps` that succeeds
at `it`, after all parsers before it failed. When all parsers fail, the error is the fold of their
errors with `combine`, from left to right; when `ps` is empty, it is `Error.unexpected it none`. -/
@[spec] theorem Spec.first [Error ε ι τ] (ps : List (Parser ε ι τ α)) (combine : ε → ε → ε)
  (it : Iter (α := ι) τ)
    : Triple (ParseIt.first ps combine : Parser ε ι τ α)
      (fun s => s.it = it ∧ s.rest = it)
      (fun a s => s.it = it ∧
        ∃ (pre post : List (Parser ε ι τ α)) (q : Parser ε ι τ α) (h : Progress s.rest it),
          ps = pre ++ q :: post ∧ (∀ q' ∈ pre, ∃ e', q' it = .error e') ∧
          q it = .ok s.rest h a)
      (fun e => (ps = [] ∧ e = Error.unexpected it none)
        ∨ ∃ (e₀ : ε) (es : List ε),
          ps.map (fun q => q it) = (e₀ :: es).map (fun e' => (.error e' : Result ε it α)) ∧
          e = es.foldl combine e₀) :=
  Triple.intro (by
    simp only [Order.PartialOrder.rel, WP.wp, WP.trans, Parser.run]
    rintro ⟨sit, srest, sp⟩ ⟨hit, hrest⟩
    dsimp only at hit hrest ⊢
    subst hit hrest
    generalize hr : (ParseIt.first ps combine : Parser ε ι τ α) srest = r
    rcases first_of_eq ps combine srest hr with
      ⟨pre, post, q, rest, p, a, hps, hpre, hq, rfl⟩ | ⟨hps, rfl⟩ | ⟨e, es, hes, rfl⟩
    · exact ⟨rfl, pre, post, q, p, hps, hpre, hq⟩
    · exact .inl ⟨hps, rfl⟩
    · exact .inr ⟨e, es, hes, rfl⟩)
