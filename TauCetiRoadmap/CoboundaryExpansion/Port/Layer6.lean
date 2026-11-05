/-
Author: Jeromie Beasley (dicipler-pixel). Port drafted with AI assistance (Grok Bot).
-/
import TauCetiRoadmap.CoboundaryExpansion.Port.Bridge
import TauCetiRoadmap.CoboundaryExpansion.K3.Replication

/-!
# Layer 6: the complete complex with permutation coefficients

The roadmap's Layer 6 (README 6.1–6.3) for the roadmap's own `Cochain`, `movedNorm`, `gaugeDist`
and `h1`, transported from `CoboundaryK3` (Beasley, Proposition 5, Theorem 4 and Appendix A,
Corollary 7) through `Port.Bridge`. Nothing here uses Kozlov's staircases (`K3.Staircase`) or
any roadmap Layer 7 statement. README 6.4 (coefficient subgroups at `k = 4`) is not covered.

* 6.1: `seed`, `seed_defect`, `seed_cost_ge`, `seed_cost_one`, `seed_gaugeDist`,
  `h1_complete_fin_four`;
* 6.2: `h1_complete_movedNorm_fin_three_of_four_dvd`;
* 6.3: `witness5` … `witness8` with their `_defect`, `_gaugeDist`, and `h1_complete_fin_five`
  … `h1_complete_fin_eight`.
-/

open Finset Equiv

namespace TauCetiRoadmap.CoboundaryExpansion.Port

open TauCetiRoadmap.CoboundaryExpansion

/-! ## 6.1 The seed -/

/-- The seed on `complete (Fin 4)`: the identity on the three edges at `0`, and the three
transpositions `(0 2 1)`, `(1 0 2)`, `(2 1 0)` on `{1,2}`, `{1,3}`, `{2,3}`. -/
def seed : Cochain (complete (Fin 4)) (Perm (Fin 3)) := ofFin (OrderIso.refl _) CoboundaryK3.w4

/-- The seed's values on the edges `u < v`, as described in README 6.1. -/
theorem seed_values :
    seed.toFun 0 1 = 1 ∧ seed.toFun 0 2 = 1 ∧ seed.toFun 0 3 = 1 ∧
      seed.toFun 1 2 = swap 1 2 ∧ seed.toFun 1 3 = swap 0 1 ∧ seed.toFun 2 3 = swap 0 2 := by
  decide

theorem seed_defect : seed.defect (movedNorm (Fin 3)) = 8 := by
  rw [seed, defect_ofFin, CoboundaryK3.witness_k4.1]; norm_num

/-- Every gauge costs at least `6`. -/
theorem seed_cost_ge (β : Fin 4 → Perm (Fin 3)) : 6 ≤ seed.cost (movedNorm (Fin 3)) β := by
  rw [cost_eq (OrderIso.refl _)]
  exact_mod_cast CoboundaryK3.witness_k4.2.1 _

/-- The identity gauge costs `6`. -/
theorem seed_cost_one : seed.cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [cost_eq (OrderIso.refl _), seed, toFin_ofFin, cost_val]
  exact_mod_cast CoboundaryK3.witness_k4.2.2.1

theorem seed_gaugeDist : seed.gaugeDist (movedNorm (Fin 3)) = 6 := by
  rw [seed, gaugeDist_ofFin, CoboundaryK3.gaugeDist_w4]; norm_num

/-- **README 6.1.** `h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4/3` (Beasley, Proposition 5). -/
theorem h1_complete_fin_four : h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4 / 3 := by
  rw [h1_eq (OrderIso.refl _), CoboundaryK3.h1_eq_k4]

/-! ## 6.2 Every multiple of four -/

/-- **README 6.2.** `h1 (complete V) (movedNorm (Fin 3)) = card V / 3` whenever `4 ∣ card V` and
`card V ≥ 4` (Beasley, Corollary 7: the replicated seed, `defect = 8q³`, `gaugeDist = 6q²`). -/
theorem h1_complete_movedNorm_fin_three_of_four_dvd {V : Type*} [Fintype V] [LinearOrder V]
    (h4 : 4 ∣ Fintype.card V) (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  obtain ⟨q, hq⟩ := h4
  rw [h1_eq (Fintype.orderIsoFinOfCardEq V hq), CoboundaryK3.h1_eq_four_mul q (by omega), hq]

/-! ## 6.3 Explicit witnesses for `k = 5, …, 8` -/

/-- The README 6.3 witness at `k = 5`. -/
def witness5 : Cochain (complete (Fin 5)) (Perm (Fin 3)) := ofFin (OrderIso.refl _) CoboundaryK3.w5
/-- The README 6.3 witness at `k = 6`. -/
def witness6 : Cochain (complete (Fin 6)) (Perm (Fin 3)) := ofFin (OrderIso.refl _) CoboundaryK3.w6
/-- The README 6.3 witness at `k = 7`. -/
def witness7 : Cochain (complete (Fin 7)) (Perm (Fin 3)) := ofFin (OrderIso.refl _) CoboundaryK3.w7
/-- The README 6.3 witness at `k = 8`. -/
def witness8 : Cochain (complete (Fin 8)) (Perm (Fin 3)) := ofFin (OrderIso.refl _) CoboundaryK3.w8

theorem witness5_defect : witness5.defect (movedNorm (Fin 3)) = 10 := by
  rw [witness5, defect_ofFin, CoboundaryK3.witness_k5.1]; norm_num
theorem witness5_gaugeDist : witness5.gaugeDist (movedNorm (Fin 3)) = 6 := by
  rw [witness5, gaugeDist_ofFin, CoboundaryK3.gaugeDist_w5]; norm_num
theorem witness6_defect : witness6.defect (movedNorm (Fin 3)) = 36 := by
  rw [witness6, defect_ofFin, CoboundaryK3.witness_k6.1]; norm_num
theorem witness6_gaugeDist : witness6.gaugeDist (movedNorm (Fin 3)) = 18 := by
  rw [witness6, gaugeDist_ofFin, CoboundaryK3.gaugeDist_w6]; norm_num
theorem witness7_defect : witness7.defect (movedNorm (Fin 3)) = 28 := by
  rw [witness7, defect_ofFin, CoboundaryK3.witness_k7.1]; norm_num
theorem witness7_gaugeDist : witness7.gaugeDist (movedNorm (Fin 3)) = 12 := by
  rw [witness7, gaugeDist_ofFin, CoboundaryK3.gaugeDist_w7]; norm_num
theorem witness8_defect : witness8.defect (movedNorm (Fin 3)) = 72 := by
  rw [witness8, defect_ofFin, CoboundaryK3.witness_k8.1]; norm_num
theorem witness8_gaugeDist : witness8.gaugeDist (movedNorm (Fin 3)) = 27 := by
  rw [witness8, gaugeDist_ofFin, CoboundaryK3.gaugeDist_w8]; norm_num

/-- **README 6.3, `k = 5`.** -/
theorem h1_complete_fin_five : h1 (complete (Fin 5)) (movedNorm (Fin 3)) = 5 / 3 := by
  rw [h1_eq (OrderIso.refl _), CoboundaryK3.h1_eq_k5]
/-- **README 6.3, `k = 6`.** -/
theorem h1_complete_fin_six : h1 (complete (Fin 6)) (movedNorm (Fin 3)) = 6 / 3 := by
  rw [h1_eq (OrderIso.refl _), CoboundaryK3.h1_eq_k6]
/-- **README 6.3, `k = 7`.** -/
theorem h1_complete_fin_seven : h1 (complete (Fin 7)) (movedNorm (Fin 3)) = 7 / 3 := by
  rw [h1_eq (OrderIso.refl _), CoboundaryK3.h1_eq_k7]
/-- **README 6.3, `k = 8`.** -/
theorem h1_complete_fin_eight : h1 (complete (Fin 8)) (movedNorm (Fin 3)) = 8 / 3 := by
  rw [h1_eq (OrderIso.refl _), CoboundaryK3.h1_eq_k8]

end TauCetiRoadmap.CoboundaryExpansion.Port
