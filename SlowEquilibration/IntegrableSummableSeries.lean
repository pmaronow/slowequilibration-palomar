-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integrability of literal Banach-valued series from summable expected norms. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.IntegrableSummableSeries
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem integrable_tsum {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NormedAddCommGroup E] [CompleteSpace E] {F : ℕ → Ω → E}
    (hF : ∀ p,Integrable (F p) P)
    (hs : Summable (fun p => ∫ ω,‖F p ω‖ ∂P)) :
    Integrable (fun ω => ∑' p,F p ω) P := by
  let hmem (p : ℕ) : MemLp (F p) 1 P := memLp_one_iff_integrable.mpr (hF p)
  let Z (p : ℕ) : Lp E 1 P := (hmem p).toLp (F p)
  have he (p : ℕ) : ‖Z p‖ₑ=ENNReal.ofReal (∫ ω,‖F p ω‖ ∂P) := by
    rw [Lp.enorm_toLp,eLpNorm_one_eq_lintegral_enorm (hF p).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm (hF p)]
  have hen : ∑' p,‖Z p‖ₑ≠⊤ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => integral_nonneg (fun _ => norm_nonneg _)) hs]
    exact ENNReal.ofReal_ne_top
  have hc : ∀ᵐ ω ∂P,∀ p,Z p ω=F p ω := by
    rw [ae_all_iff]
    exact fun p => (hmem p).coeFn_toLp
  have hae : (∑' p,Z p : Lp E 1 P) =ᵐ[P] (fun ω => ∑' p,F p ω) := by
    filter_upwards [Lp.coeFn_tsum hen,hc] with ω hω he
    rw [hω]
    exact tsum_congr he
  exact memLp_one_iff_integrable.mp ((Lp.memLp _).ae_eq hae)

end SlowEquilibration.IntegrableSummableSeries
