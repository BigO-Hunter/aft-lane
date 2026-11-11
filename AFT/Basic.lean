/-
Copyright (c) 2026 the MultiAgency body. All rights reserved.
-/
import Mathlib.Order.FixedPoints
import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic

/-!
# Approximation Fixpoint Theory — core construction (road 3, scoping)

Approximators for non-monotone operators over a complete lattice, following the
restatement of AFT's ultimate approximation in Rasheed–Garg 2026
([arXiv:2605.06803](https://arxiv.org/abs/2605.06803)), which itself restates the
ultimate approximation of Denecker–Marek–Truszczyński
(*Information and Computation*, DOI 10.1016/j.ic.2004.02.004).

## Main definitions

* `AFT.envUpper f` — the best monotone over-approximation of `f`:
  `f^u(x) = ⨆ {f y | y ≤ x}`.
* `AFT.envLower f` — the best monotone under-approximation of `f`:
  `f^ℓ(x) = ⨅ {f y | x ≤ y}`.
* `AFT.Sound f lo hi` — the bound `[lo, hi]` contains a fixed point of `f`.

## Main results

* `AFT.envUpper_mono`, `AFT.envLower_mono` — **both** envelopes are monotone for
  *any* operator `f`, even a fully non-monotone one: monotonicity emerges from the
  construction and is never assumed of the operator. This is the load-bearing fact
  for our speculative-update engine class.
* `AFT.mem_aft_bound` — **Theorem 4.2** of Rasheed–Garg (the anytime sound bound):
  every fixed point `μ` of `f` satisfies `lfp (envLower f) ≤ μ ≤ gfp (envUpper f)`
  (with `lfp`/`gfp` the bundled `OrderHom` fixed points of this Mathlib pin).
* `AFT.aft_bound_sound` — the initial AFT bound is sound (given `f` has a fixed
  point at all).
* `AFT.envUpper_eq_const_of_antitone`, `AFT.envLower_eq_const_of_antitone`,
  `AFT.fixedPoint_bounds_of_antitone` — the anti-monotone specialization (the
  shape of the speculative-analysis operator of Rasheed–Garg §7): the whole AFT
  bound collapses to the one-step bound `[f ⊤, f ⊥]`.
-/

namespace AFT

open CompleteLattice

variable {α : Type*} [CompleteLattice α]

/-- The best monotone over-approximation of `f`:
`f^u(x) = ⨆ {f y | y ≤ x}`.
Monotone for *any* `f` (`envUpper_mono`); pointwise dominates `f`
(`le_envUpper`). -/
def envUpper (f : α → α) (x : α) : α := sSup (f '' {y | y ≤ x})

/-- The best monotone under-approximation of `f`:
`f^ℓ(x) = ⨅ {f y | x ≤ y}`.
Monotone for *any* `f` (`envLower_mono`); pointwise under-estimates `f`
(`envLower_le`). -/
def envLower (f : α → α) (x : α) : α := sInf (f '' {y | x ≤ y})

/-- Monotonicity of the upper envelope — free for any `f`, monotone or not. -/
lemma envUpper_mono (f : α → α) : Monotone (envUpper f) := by
  intro x x' h
  refine sSup_le_sSup fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨y, le_trans hy h, rfl⟩

/-- Monotonicity of the lower envelope — free for any `f`, monotone or not. -/
lemma envLower_mono (f : α → α) : Monotone (envLower f) := by
  intro x x' h
  refine le_sInf fun z hz => ?_
  obtain ⟨y, hy, rfl⟩ := hz
  exact sInf_le ⟨y, le_trans h hy, rfl⟩

/-- `f` never exceeds its upper envelope. -/
lemma le_envUpper (f : α → α) (x : α) : f x ≤ envUpper f x :=
  le_sSup ⟨x, le_refl x, rfl⟩

/-- The lower envelope never exceeds `f`. -/
lemma envLower_le (f : α → α) (x : α) : envLower f x ≤ f x :=
  sInf_le ⟨x, le_refl x, rfl⟩

/-- The upper envelope as a bundled monotone map — free for any `f`.
This is the fact that re-admits Knaster–Tarski into the non-monotone world. -/
def envUpperHom (f : α → α) : α →o α := ⟨envUpper f, envUpper_mono f⟩

/-- The lower envelope as a bundled monotone map — free for any `f`. -/
def envLowerHom (f : α → α) : α →o α := ⟨envLower f, envLower_mono f⟩

/-- A bound `[lo, hi]` is *sound* (Rasheed–Garg Def. 5.2) if it contains some
fixed point of `f`. -/
def Sound (f : α → α) (lo hi : α) : Prop :=
  ∃ μ, Function.IsFixedPt f μ ∧ lo ≤ μ ∧ μ ≤ hi

/-- **Theorem 4.2** of Rasheed–Garg 2026 — the anytime sound bound.
Every fixed point `μ` of `f` lies inside the initial AFT bound
`[lfp (envLowerHom f), gfp (envUpperHom f)]`. These are the tightest bounds
obtainable by the tightest sound interval transformer (the well-founded
approximation, Denecker–Marek–Truszczyński 2004). -/
theorem mem_aft_bound (f : α → α) {μ : α} (hμ : Function.IsFixedPt f μ) :
    OrderHom.lfp (envLowerHom f) ≤ μ ∧ μ ≤ OrderHom.gfp (envUpperHom f) := by
  have h : f μ = μ := hμ
  constructor
  · refine OrderHom.lfp_le (envLowerHom f) ?_
    calc envLower f μ ≤ f μ := envLower_le f μ
      _ = μ := h
  · refine OrderHom.le_gfp (envUpperHom f) ?_
    calc μ = f μ := h.symm
      _ ≤ envUpper f μ := le_envUpper f μ

/-- The initial AFT bound is sound whenever `f` has any fixed point. -/
theorem aft_bound_sound (f : α → α) (hf : ∃ μ, Function.IsFixedPt f μ) :
    Sound f (OrderHom.lfp (envLowerHom f)) (OrderHom.gfp (envUpperHom f)) := by
  obtain ⟨μ, hμ⟩ := hf
  exact ⟨μ, hμ, mem_aft_bound f hμ⟩

/-! ### The anti-monotone specialization (the speculative-update engine class)

The operator Rasheed–Garg §7 extract from speculative program analysis is
*anti-monotone*: more assumptions yield a more precise analysis, which refutes
more assumptions. For an antitone `f` the envelopes are constant and the whole
AFT bound collapses to `[f ⊤, f ⊥]` in a single step. -/

/-- For antitone `f`, the upper envelope is the constant `f ⊥`:
every term `f y` with `y ≤ x` obeys `f y ≤ f ⊥` (antitonicity from `⊥ ≤ y`),
and `⊥` itself is in the range. -/
lemma envUpper_eq_const_of_antitone {f : α → α} (hf : Antitone f) :
    envUpper f = fun _ => f ⊥ := by
  funext x
  show envUpper f x = f ⊥
  apply le_antisymm
  · refine sSup_le fun v hv => ?_
    obtain ⟨y, _, rfl⟩ := hv
    exact hf bot_le
  · exact le_sSup ⟨⊥, bot_le, rfl⟩

/-- For antitone `f`, the lower envelope is the constant `f ⊤`:
every term `f y` with `x ≤ y` obeys `f ⊤ ≤ f y` (antitonicity from `y ≤ ⊤`),
and `⊤` itself is in the range. -/
lemma envLower_eq_const_of_antitone {f : α → α} (hf : Antitone f) :
    envLower f = fun _ => f ⊤ := by
  funext x
  show envLower f x = f ⊤
  apply le_antisymm
  · exact sInf_le ⟨⊤, le_top, rfl⟩
  · refine le_sInf fun v hv => ?_
    obtain ⟨y, _, rfl⟩ := hv
    exact hf le_top

/-- Antitone operators: every fixed point sits in the one-step bound
`[f ⊤, f ⊥]`. Direct specialization of `mem_aft_bound`. -/
theorem fixedPoint_bounds_of_antitone {f : α → α} (hf : Antitone f) {μ : α}
    (hμ : Function.IsFixedPt f μ) : f ⊤ ≤ μ ∧ μ ≤ f ⊥ := by
  have h : f μ = μ := hμ
  constructor
  · calc f ⊤ ≤ f μ := hf le_top
      _ = μ := h
  · calc μ = f μ := h.symm
      _ ≤ f ⊥ := hf bot_le

end AFT
