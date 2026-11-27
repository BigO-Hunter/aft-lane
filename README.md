# aft-lane

Scoping + first construction for **road 3: Approximation Fixpoint Theory (AFT)** —
anytime guaranteed bounds for certified-settling algorithms. Siblings: road 1
(per-event certification) and road 2 (global potential —
[bonifaci-lane](https://github.com/BigO-Hunter/bonifaci-lane)).

**Why AFT fits the campaign:** our uncapped/speculative-update engine class (the
speculative-iteration families in the SSSP/APSP work) settles under *non-monotone*
update operators — classical Knaster–Tarski does not apply. AFT (Denecker, logic
programming lineage) supplies **anytime, guaranteed bounds** for exactly that class:
every settle point provably lies in `[lfp(envLower), gfp(envUpper)]`, and iterative
refinement shrinks the interval while preserving soundness (Rasheed–Garg 2026).

* **Ledger (read this first):** [STMTS.md](STMTS.md) — verified primary source,
  claims extraction, fit analysis, statement-fidelity table, milestone map M0–M5,
  citation ledger, incidents.
* **Pins:** Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
  (campaign family — cloned from bonifaci-lane's build).
* **Primary (verified):** arXiv:2605.06803, Rasheed & Garg (UT Austin),
  *Bounding Fixed Points of Non-Monotone Processes: Theory to Practice*, cs.PL,
  7 May 2026, DOI `10.48550/arXiv.2605.06803`. Full PDF + HTML in [refs/](refs/).

## Module family (`AFT/` — namespace per lane brief)

| File | Contents | Status |
|---|---|---|
| `AFT/Basic.lean` | `envUpper` / `envLower` (best monotone envelopes), monotone-pair closure (`envUpper_mono`/`envLower_mono` — free for any `f`), `Sound`, `mem_aft_bound` (Thm 4.2, the anytime bound), `aft_bound_sound`, antitone specialization (`envUpper_eq_const_of_antitone`, `fixedPoint_bounds_of_antitone`) | **built, no `sorry`, no axioms** |
| `AFT/Refine.lean` | refinement operator `F` on bounds, Lemma 5.3 (soundness preservation), 5.4 (shrinking), prune criterion | M2 (next) |

## Build

Standard `lake build AFT` against the shared campaign Mathlib (`.lake` is an APFS
clone of `bonifaci-lane`'s build; re-clone if swept). Build discipline: swap gate
(`vm.swapusage` used > 12 GB ⇒ wait — `receipts/gated_build.py` polls + holds the
lock via `fcntl` since this host has no `flock` binary), receipts to `receipts/`.

## Credit

Theory: Denecker–Marek–Truszczyński (AFT, 2000/2004); the practical refinement +
branch-and-bound layer: Rasheed & Garg (2026). Formalization: this lane, 2026-11-11.

## What work can be done here

M1 (`AFT/Basic.lean`) is built green. Next: M2 `AFT/Refine.lean` — refinement operator F, Lemma 5.3 (soundness preservation), Lemma 5.4 (shrinking), prune criterion; then the milestone map M3–M5 in the lane brief. Reproduction: `lake build AFT` against the campaign Mathlib pin (v4.34.1 / d13f23b7); swap-gated build discipline via `receipts/gated_build.py`.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work).

---

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com). Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).