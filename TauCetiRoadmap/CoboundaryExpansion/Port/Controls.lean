/-
Author: Jeromie Beasley (dicipler-pixel). Port drafted with AI assistance (Grok Bot). The ported
`K3` files were drafted with Grok Bot and Claude (see `K3/Replication.lean`).
-/
import TauCetiRoadmap.CoboundaryExpansion.Port.Layer6
import TauCetiRoadmap.CoboundaryExpansion.Port.Layer8

/-!
# Negative controls

Wrong constants are refuted outright, so the equalities of `Layer6` and `Layer8` are not vacuous.
-/

namespace TauCetiRoadmap.CoboundaryExpansion.Port

open TauCetiRoadmap.CoboundaryExpansion

theorem h1_complete_fin_four_ne_three_halves :
    h1 (complete (Fin 4)) (movedNorm (Fin 3)) ≠ 3 / 2 := by
  rw [h1_complete_fin_four]; norm_num

theorem h1_complete_ne_half {V : Type*} [Fintype V] [LinearOrder V] (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) ≠ (Fintype.card V : ℝ) / 2 := by
  rw [h1_complete_movedNorm_fin_three hV]
  have : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  intro h; linarith

theorem seed_gaugeDist_ne_five : seed.gaugeDist (movedNorm (Fin 3)) ≠ 5 := by
  rw [seed_gaugeDist]; norm_num

end TauCetiRoadmap.CoboundaryExpansion.Port
