/-
Author: Jeromie Beasley (dicipler-pixel). Port drafted with AI assistance (Grok Bot). The ported
`K3` files were drafted with Grok Bot and Claude (see `K3/Replication.lean`).
-/
import TauCetiRoadmap.CoboundaryExpansion.Port.Bridge
import TauCetiRoadmap.CoboundaryExpansion.K3.Staircase

/-!
# Layer 8: the headline, for the roadmap's own definitions

`h1_complete_movedNorm_fin_three` and `h1Norm_complete_movedNorm_fin_three`, with the exact
statements of `Suggested.lean` (checked by `example`s at the end of this file).

Route: `Port.h1_eq_card` reduces to `CoboundaryK3.h1_eq_all` (Beasley, Theorem 8), which uses the
replicated `k = 4` seed at multiples of four and replicated `Sym(3)` staircase seeds on
`K_{2t+1}` elsewhere. The staircase seeds are `Sym(3)`-valued cochains whose gauge distance is
proved directly (parity of the gauge, then a cut count); the roadmap's Layer 7 theorem
`h1_complete_movedNorm_fin_two` (the `𝔽₂` constant) is neither stated nor used. `h1Sym_complete`
(which needs the Layer 4 star bound in every degree) is not proved here.

This is an alternative route to README 8.1, whose listed dependency is 7.4 (Kozlov's `𝔽₂`
theorem); 7.4 is not used.

Attribution: the seeds are Kozlov's staircase graphs [D. N. Kozlov, arXiv:1610.07136, Def. 3.2
and §3.1]; the cut-minimality bound is proved directly here, following [Kozlov, Lemma 3.8 and
Cor. 3.13] (triangle count after [Kozlov, Lemma 3.10]); the `Sym(3)` transfer (parity retraction)
and the `k/3` theorem are [Beasley, Cor. 7, Thm. 8].
-/

open Finset Equiv

namespace TauCetiRoadmap.CoboundaryExpansion.Port

open TauCetiRoadmap.CoboundaryExpansion

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **Layer 8.1.** The permutation coboundary constant of the complete complex is `k/3` for every
`k ≥ 4`, attained with values in `Sym(3)`. -/
theorem h1_complete_movedNorm_fin_three (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  rw [h1_eq_card]
  exact CoboundaryK3.h1_eq_all _ (by omega)

/-- **Layer 8.1, normalized.** `(k choose 2) / (k choose 3) · k/3 = k/(k-2)`. -/
theorem h1Norm_complete_movedNorm_fin_three (hV : 4 ≤ Fintype.card V) :
    h1Norm (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / (Fintype.card V - 2) := by
  unfold h1Norm
  rw [h1_complete_movedNorm_fin_three hV]
  simp only [complete, Finset.card_powersetCard, Finset.card_univ]
  set n := Fintype.card V with hn
  have h3 := Nat.choose_succ_right_eq n 2
  have hpos : 0 < n.choose 3 := Nat.choose_pos (by omega)
  have hR : ((n.choose 3 : ℕ) : ℝ) * 3 = (n.choose 2 : ℝ) * ((n : ℝ) - 2) := by
    have h3' : ((n.choose (2 + 1) * (2 + 1) : ℕ) : ℝ) = ((n.choose 2 * (n - 2) : ℕ) : ℝ) :=
      congrArg _ h3
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)] at h3'
    linarith
  have hC3 : ((n.choose 3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hn2 : (n : ℝ) - 2 ≠ 0 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hV
    linarith
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hC3 (by norm_num)) hn2]
  linear_combination (-(n : ℝ)) * hR

end TauCetiRoadmap.CoboundaryExpansion.Port

/-! ## The statements are exactly those of `Suggested.lean` -/

section StatementCheck

open TauCetiRoadmap.CoboundaryExpansion

example : @TauCetiRoadmap.CoboundaryExpansion.Port.h1_complete_movedNorm_fin_three =
    @TauCetiRoadmap.CoboundaryExpansion.h1_complete_movedNorm_fin_three := rfl

example : @TauCetiRoadmap.CoboundaryExpansion.Port.h1Norm_complete_movedNorm_fin_three =
    @TauCetiRoadmap.CoboundaryExpansion.h1Norm_complete_movedNorm_fin_three := rfl

end StatementCheck
