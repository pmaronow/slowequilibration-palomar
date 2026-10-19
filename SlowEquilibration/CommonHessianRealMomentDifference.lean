-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianRealMomentPerturbation

/-! Ordinary real absolute-moment bounds for actual random differences. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem integral_absolute_moment_difference {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (F G:Ω→ℝ) (hF:Measurable F) (q:ℝ) (hq:0 ≤ q)
    (hG:Integrable (fun x=>|G x|^q) P)
    (hDiff:Integrable (fun x=>|F x-G x|^q) P) :
    Integrable (fun x=>|F x|^q) P ∧
      (∫ x,|F x|^q ∂P) ≤ (2:ℝ)^q*((∫ x,|G x|^q ∂P)+(∫ x,|F x-G x|^q ∂P)):=by
  let R:=fun x=>(2:ℝ)^q*(|G x|^q+|F x-G x|^q)
  have hR:Integrable R P:=(hG.add hDiff).const_mul ((2:ℝ)^q)
  have hp (x):|F x|^q ≤ R x:=by
    have hab:|F x| ≤ |G x|+|F x-G x|:=by
      simpa only [show G x+(F x-G x)=F x by ring] using abs_add_le (G x) (F x-G x)
    exact (Real.rpow_le_rpow (abs_nonneg _) hab hq).trans
      (nonnegative_add_rpow_bound (abs_nonneg _) (abs_nonneg _) hq)
  have hi:Integrable (fun x=>|F x|^q) P:=hR.mono' (hF.abs.pow_const q).aestronglyMeasurable
    (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)];exact hp x))
  refine ⟨hi,(integral_mono hi hR hp).trans_eq ?_⟩
  dsimp only [R]
  rw [integral_const_mul,integral_add hG hDiff]

end
end SlowEquilibration.GaussianQuadraticVariance
