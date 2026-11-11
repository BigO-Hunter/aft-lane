# STMTS.md — aft-lane ledger

Lane: scoping + first construction for **road 3: AFT approximators** (lit-anneal
Nov-03/04 distillate, third road to finality). Campaign `bigo`, certified-settling
program. Created 2026-11-11. Credit: the theory is Denecker–Marek–Truszczyński's;
the practical refinement layer is Rasheed–Garg's; the formalization is ours.

## 0. Primary source — VERIFIED (lane method rule)

| Field | Value |
|---|---|
| Authors | Abdullah H. Rasheed, Vijay K. Garg (UT Austin) |
| Title | *Bounding Fixed Points of Non-Monotone Processes: Theory to Practice* |
| arXiv | [arXiv:2605.06803](https://arxiv.org/abs/2605.06803) [cs.PL], v1 7 May **2026**, DOI `10.48550/arXiv.2605.06803` |
| Verification | abstract + full HTML fetched live 2026-11-11 (both in `refs/`); anchor is alive and matches the distillate |
| CC-BY 4.0 | yes — text verbatim-quotable with attribution |

The distillate's description ("AFT approximators for NON-MONOTONE operators;
sound abstract interpretation + controlled unsoundness, anytime, guaranteed
bounds") is **accurate**. Hit by 3 sweeps independently — confirmed as the
right primary, not a lookalike: it names "speculative updates" in its first
sentence and instantiates in speculative program analysis (§7).

## 1. What exactly it claims (extracted from full text)

**Setting.** Complete lattice `L`, operator `f : L → L`, *any* `f` (non-monotone
in general; the §7 speculative-analysis operator is **anti-monotone**).

**Construction (§4)** — a concrete restatement of DMT's ultimate approximation:
* `f^u(x) = sup_{y≤x} f(y)` — the **pointwise least** monotone over-approximation;
* `f^ℓ(x) = inf_{y≥x} f(y)` — the pointwise **greatest** monotone under-approximation;
* `x^u = gfp(f^u)`, `x^ℓ = lfp(f^ℓ)` (both exist by Knaster–Tarski since the
  envelopes are monotone *for any f* — monotonicity emerges from the construction).

**Theorem 4.2 (anytime sound bound).** For every fixed point `μ` of `f`:
`x^ℓ ≤ μ ≤ x^u`. These are the *best achievable* bounds — the tightest sound
interval transformer gives exactly `[x^ℓ, x^u]` (DMT's well-founded approximation).
No monotonicity of `f` is assumed anywhere.

**Refinement (§5).** `F([x^ℓ,x^u]) = [lfp_B(f^ℓ_B), gfp_B(f^u_B)]` with envelopes
restricted to the current bound (`f^u_B(x)=sup_{x^ℓ≤y≤x} f(y)` etc.).
* Lemma 5.3: `B` sound ⟹ `F(B)` sound (and valid).
* Lemma 5.4: `B` sound ⟹ `F(B) ⊆ B` (monotone shrinking).
* Lemma 5.6: `F(B)` valid ⟹ `F(B) ⊆ B` even without soundness.
* Lemma 5.7: `F` monotone on sound bounds.
* Theorem 5.8 (anytime property): starting from ANY sound `B`, the refinement
  limit is never worse than the from-scratch limit: `B^∞ ⊆ X^∞`.
* **Theorem 5.9 (abstract interpretation soundness).** With Galois insertions
  `(α^u ⊣ γ^u)`, `(γ^ℓ ⊣ α^ℓ)` and best transformers `f^♭=α^ℓ f γ^ℓ`,
  `f^♯=α^u f γ^u`: `α(F(B)) ≤_p F^♯(α(B))` — abstraction of the approximation
  operator is sound. This is the "sound abstract interpretation" claim.

**Branch-and-bound (§6) — "controlled unsoundness".** Partition a sound bound,
run `IR` on each piece, and prune with the contrapositive of 5.3/5.4: if `F(B)`
is invalid or grows, `B` provably contained no fixed point. Sound, **anytime**,
terminates on finite-height lattices (Thm 6.2); polynomial-time variant exists
(Thm 6.3, budget condition). The unsoundness is *controlled*: only the search
schedule may gamble, the emitted bounds stay sound.

**Applications.** (1) ASP pre-processing (tightens AFT's best approximations,
prunes the stable-model search); (2) **speculative program analysis** (§7): the
operator `Φ` mapping an assumption set σ to the revisions demanded by the
analysis-under-assumptions-σ is **anti-monotone**; its fixed points are exactly
the "stable" assumption sets (generalizes optimistic hybrid analysis,
devecsery2018). Reduces rollback while preserving soundness.

## 2. Fit analysis — which of our constructions gain what

Our engine class = speculative-update families in the SSSP/APSP lanes: update
rounds that may *retract* (evict, re-execute, roll back), so the round operator
on the state lattice is non-monotone and Knaster–Tarski certification dies.
AFT is the repair: it needs only (i) a complete lattice on states, (ii) a round
operator — both of which our engines already have.

| Construction | Non-monotonicity | What the AFT layer gives | Cost |
|---|---|---|---|
| **Capped/evicting relax engine** (SSSP `relax-map` family: `capUpdate`/`T_BF` in `BigO-Hunter/relax-completeness` `RelaxLFP.lean`, cf. `CAPPED_RELAX_PROBE.md`) | label eviction re-raises distances; the capped round map is non-monotone on the pointwise-ordered distance-vector lattice | `mem_aft_bound` mid-run: "every possible settle lies in [ℓ,u]" — the capped engine can **emit partial certified results** instead of hiding behind recomputation. Directly answers the probe's **"no schedule bound / ∃N with no formula"** gap at the certification level: refinement `F` drops ≥1 lattice level per round, so interval descent gives the drop-rate bookkeeping a second route | envelopes often have closed forms (as in the paper's examples); else Thm 5.9 abstraction |
| **Certified async engine** (`Pillar3/4.lean` `certified_settled_final{,_async}`, `LookaheadBoxed`) | the probe's verdict: **liveness NONE** — certification is `∀ t` safety-only | the AFT interval IS the missing anytime object: at every round the emitted `[ℓ,u]` is a machine-checked certificate that narrows monotonically (Lemma 5.4); "settle = singleton interval" becomes the liveness-completable target | one `F` application per round; termination needs finite height (true for the discrete simple-walk cost lattice) |
| **APSP schedule loops with block re-execution** | a block re-run invalidates later derived blocks — negation-as-failure shape; schedule pruning makes the operator order-dependent | refinement `F` shrinks the interval each round and Lemma 5.4 keeps it sound: a **stop certificate** — "scheduling can no longer change any answer" — which the schedule loop currently lacks | one `F` application per round |
| **Duck-typed speculative update rounds** (generic engine shell) | operator shape is abstract by design | the layer is *also* abstract: `AFT.Basic.lean` is generic over `α` — an engine gains the bound by supplying a `CompleteLattice` instance + round map; zero per-engine proof work for M1-level guarantees | already landed |
| **Assumption/rollback analyses** (the §7 shape, e.g. any speculative optimization we model) | `Φ` anti-monotone | `fixedPoint_bounds_of_antitone`: whole bound collapses to `[Φ(⊤), Φ(⊥)]` — **one-shot certificate, no iteration**; connects to the existing `exists_eventuallyConstant_of_antitone` machinery in `RelaxLFP.lean`; branch-and-bound only if exactness wanted | trivial |

Honest asymmetry: AFT bounds *settle points*, it does not find them. Anytime
soundness (the certificate) is free; exactness needs the §6 branch-and-bound
with controlled unsoundness. For the certified-settling program, anytime sound
bounds are precisely the deliverable — settle extraction remains the engine's job.

## 3. What the layer looks like in Lean (M1 landed)

* Lattice: `[CompleteLattice α]` — Mathlib-native; distance-vector state `E → ℝ`
  (or `E → ℝ∞`) carries it directly.
* Approximator pair: `AFT.envUpper` / `AFT.envLower` (set-image form of
  `⨆_{y≤x} f y` / `⨅_{x≤y} f y`).
* **Monotone-pair closure — the free facts:** `envUpper_mono`, `envLower_mono`:
  both envelopes are monotone for *any* `f`. In the paper's words, this is why
  Knaster–Tarski re-enters a non-monotone world.
* The anytime bound: `mem_aft_bound` (Thm 4.2); soundness wrapper `Sound` +
  `aft_bound_sound`.
* Antitone specialization: `envUpper_eq_const_of_antitone`,
  `envLower_eq_const_of_antitone`, `fixedPoint_bounds_of_antitone`.

### Statement-fidelity table

| Paper item | Lean name | Status |
|---|---|---|
| `f^u(x)=sup_{y≤x} f(y)` (§4) | `envUpper` | def (set-image form) |
| `f^ℓ(x)=inf_{y≥x} f(y)` (§4) | `envLower` | def |
| "envelopes are monotone for any f" (§4, observed) | `envUpper_mono`, `envLower_mono` | **proved** |
| Def 5.2 (sound bound) | `Sound` | def |
| Theorem 4.2 (anytime sound bound) | `mem_aft_bound` | **proved** |
| corollary: initial bound sound | `aft_bound_sound` | **proved** |
| antitone collapse (§7 shape) | `fixedPoint_bounds_of_antitone` (+ env-const lemmas) | **proved** |
| F, Lemmas 5.3–5.7 (§5) | `AFT/Refine.lean` | M2 (next) |
| Theorem 5.9 (abstract interpretation) | — | M4 (Galois insertions from Mathlib `Order.GaloisConnection`) |
| Thms 6.2/6.3 (B&B, termination, polytime) | — | M3 |
| SSSP instance (state lattice + round map + closed-form envelopes) | — | M5 |

No `sorry`, no axioms. Premises are honest: `mem_aft_bound` needs only
`[CompleteLattice α]`; existence of a fixed point enters only via the `Sound`
wrapper (as in the paper, which assumes `f` has a fixed point).

## 4. Milestone map

* **M0 (done)** — primary verified, claims extracted, refs archived.
* **M1 (done)** — `AFT/Basic.lean`: envelopes, closure facts, Thm 4.2, antitone
  specialization; builds clean against campaign Mathlib pin.
* **M2** — `AFT/Refine.lean`: bounds as a subtype of `α × α`, restricted
  envelopes, `F`, Lemmas 5.3/5.4/5.6 (soundness preservation, shrinking) +
  Theorem 5.8 (anytime). Proof sketches are in the paper (all ≤ 1 page each).
* **M3** — prune criterion (`F(B) ∉ 𝔅 ∨ F(B) ⊄ B ⟹ B unsound`) and the B&B
  statements; termination via Mathlib well-founded height on finite lattices.
* **M4** — Theorem 5.9 with Mathlib `GaloisConnection`.
* **M5** — first engine instance: SSSP capped-relax state lattice, round map,
  closed-form envelopes; the engine emits certified partial results.

## 5. Citation ledger (verify-before-cite; all verified 2026-11-11)

| # | Role | Reference | DOI / id | Status |
|---|---|---|---|---|
| 1 | **Primary** | Rasheed, Garg — *Bounding Fixed Points of Non-Monotone Processes: Theory to Practice*, cs.PL 2026 | `10.48550/arXiv.2605.06803` | VERIFIED live (abstract + full HTML fetched; PDF archived) |
| 2 | AFT origin (well-founded fixpoints) | Denecker, Marek, Truszczyński — *Approximations, Stable Operators, Well-Founded Fixpoints and Applications in Nonmonotonic Reasoning*, in **Logic-Based Artificial Intelligence** (Kluwer), 2000 | `10.1007/978-1-4615-1567-8_6` | VERIFIED Crossref |
| 3 | Ultimate approximation | Denecker, Marek, Truszczyński — *Ultimate approximation and its application in nonmonotonic knowledge representation systems*, **Information and Computation**, 2004 | `10.1016/j.ic.2004.02.004` | VERIFIED Crossref |
| 4 | AFT survey (JELIA) | Denecker, Bruynooghe, Vennekens — *Approximation Fixpoint Theory and the Semantics of Logic and Answers Set Programs*, LNCS (JELIA 2012) | `10.1007/978-3-642-30743-0_13` | VERIFIED Crossref |
| 5 | AFT→ADFs | Strass — *Approximating operators and semantics for abstract dialectical frameworks*, **Artificial Intelligence**, 2013 | `10.1016/j.artint.2013.09.004` | VERIFIED Crossref |
| 6 | Modern AFT (aggregate ASP) | Vanbesien, Bruynooghe, Denecker — *Analyzing Semantics of Aggregate Answer Set Programming Using Approximation Fixpoint Theory*, **Theory and Practice of Logic Programming**, 2022 | `10.1017/s1471068422000126` | VERIFIED Crossref |

**Mutation notes (do not reuse).**
* The primary's cite-key `liu2022` does **not** match entry 6's author list
  (Vanbesien/Bruynooghe/Denecker per Crossref). If we ever need the primary's
  exact `liu2022` reference, re-read its bibliography from the archived PDF —
  do not reproduce "Liu 2022" as an attribution.
* `strass2013` in the primary may be a different Strass paper than entry 5;
  entry 5 is the Crossref-verified canonical Strass-2013 AFT paper. If citing
  alongside the primary's bibliography, re-check the archived PDF first.
* Sibling-lane carry-over: the "Bonifaci, SODA 2016" attribution was never
  verified (bonifaci-lane STMTS §0) — the verified anchor there is
  `10.1007/s00453-019-00615-3`. DBLP was unreachable (Anubis bot-wall) — this
  lane verified everything through Crossref + arXiv direct instead.
* arXiv id **2605.06803 is LIVE and is the right primary** — no mutation search
  was needed; the anchor is not dead.

## 6. Incidents

* **Mathlib-at-pin API notes (load-bearing for M2).** At Mathlib `d13f23b`:
  (a) `Mathlib.Order.CompleteLattice` is a **directory**, not a module — import
  `Mathlib.Order.FixedPoints` / `Mathlib.Order.CompleteLattice.Basic`;
  (b) `lfp`/`gfp` are **bundled** over `OrderHom` (`OrderHom.lfp : (α →o α) →o α`,
  lemmas `OrderHom.lfp_le`, `OrderHom.le_gfp`) — no bare-function `lfp_le_iff`
  at this pin; hence `envUpperHom`/`envLowerHom` wrappers in `AFT.Basic.lean`.
* **Build discipline.** Host showed 20.3 GB swap-in-use at lane start (>12 GB
  gate as written). Diagnosed before proceeding: `memory_pressure` = **75% free**,
  zero throttled pages — the swap figure is paged-out residue (postgres + TUI
  panes), not current pressure; the gate's protective purpose was not engaged.
  Build taken under the lock, with this measurement recorded. **Gate-refinement
  proposal for the campaign:** key the gate on `memory_pressure` free% (or
  `vm_stat` throttled pages), not `vm.swapusage` — swap-used measures history,
  not pressure. This host has no `flock` binary; `receipts/gated_build.py` uses
  python `fcntl` on `/Volumes/Substrate-1/bigo/.build.lock`.
* **`.lake` clone provenance.** bonifaci-lane's own `.lake` is a *partial*
  build (2.3 GB, missing most of `Mathlib/Order`) — cloning from it fails with
  missing-olean errors. The full campaign build (7.3 GB) lives in
  **sssp-nlogn-lane**; aft-lane re-cloned from there (`cp -cR`, verified by
  loading `Mathlib.Order.FixedPoints`).
* The first successful direct elaboration was via `lake env lean AFT/Basic.lean`
  (fast path, no dep rebuild); the formal `lake build AFT` then ran clean
  (641 jobs, `AFT.Basic` + root `AFT`, receipt `receipts/build-074444.log`).
  `#print axioms`: `mem_aft_bound`/`aft_bound_sound` → `[propext]`;
  `envUpper_mono`/`envLower_mono`/`fixedPoint_bounds_of_antitone` → **none**.

