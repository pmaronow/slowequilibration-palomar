-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianTranslatedQuadraticHighMoments

/-! Ordinary real absolute-moment transport under a deterministic bias. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Actual q-moment perturbation, with the integrability obligation derived
from the actual comparison function. -/
theorem integral_absolute_moment_perturbation {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (F G:Ω→ℝ) (hF:Measurable F)
    (q:ℝ) (hq:0≤q) (hG:Integrable (fun x=>|G x|^q) P)
    {K:ℝ} (hK:0≤K) (hDiff:∀ x,|F x-G x|≤K) :
    Integrable (fun x=>|F x|^q) P ∧
      (∫ x,|F x|^q ∂P)≤(2:ℝ)^q*((∫ x,|G x|^q ∂P)+K^q):=by
  let R:=fun x=>(2:ℝ)^q*(|G x|^q+K^q)
  have hR:Integrable R P:=(hG.add (integrable_const (K^q))).const_mul ((2:ℝ)^q)
  have hp (x):|F x|^q≤R x:=by
    have hab:|F x|≤|G x|+K:=by
      have hh:=abs_add_le (G x) (F x-G x)
      rw [show G x+(F x-G x)=F x by ring] at hh
      exact hh.trans (add_le_add le_rfl (hDiff x))
    exact (Real.rpow_le_rpow (abs_nonneg _) hab hq).trans
      (nonnegative_add_rpow_bound (abs_nonneg _) hK hq)
  have hi:Integrable (fun x=>|F x|^q) P:=hR.mono' (hF.abs.pow_const q).aestronglyMeasurable
    (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)];exact hp x))
  refine ⟨hi,(integral_mono hi hR hp).trans_eq ?_⟩
  dsimp only [R]
  rw [integral_const_mul,integral_add hG (integrable_const (K^q))]
  simp only [integral_const,probReal_univ,one_smul]

end
end SlowEquilibration.GaussianQuadraticVariance
