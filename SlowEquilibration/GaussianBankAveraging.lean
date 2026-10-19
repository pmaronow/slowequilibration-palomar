-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCompactFeatureComparison
public import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine Gaussian independent-bank disintegration with an external
probability parameter, including the Fubini order needed for conditional
spherical tensor positivity. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianCompactFeatureComparison

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [MeasurableSpace X]

omit [DecidableEq ι] [DecidableEq κ] in
theorem sumJoin_sumSplit (D : EuclideanSpace ℝ (ι ⊕ κ)) : sumJoin (sumSplit D)=D := by
  ext (i|j) <;> rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem sumSplit_sumJoin (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : sumSplit (sumJoin D)=D := by
  apply Prod.ext <;> ext i <;> rfl

/-- Split the actual iid Gaussian coordinate bank and move the external
parameter integral between its genuinely independent banks. -/
theorem external_parameter_joined_gaussian_swap (π : Measure X) [IsProbabilityMeasure π]
    (F : X × EuclideanSpace ℝ (ι ⊕ κ) → ℝ) (hF : Measurable F)
    {C : ℝ} (hb : ∀p,‖F p‖≤C) :
    (∫x,∫D,F (x,D) ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ) ∂π)=
      ∫w,∫x,∫z,F (x,sumJoin (w,z))
        ∂SYK.standardGaussianMeasureOnEuclidean κ ∂π ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let γ := SYK.standardGaussianMeasureOnEuclidean ι
  let δ := SYK.standardGaussianMeasureOnEuclidean κ
  have hS : HasLaw (sumSplit (ι := ι) (κ := κ)) (γ.prod δ)
      (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)) :=
    ⟨sumSplit.continuous.measurable.aemeasurable,sumSplit_gaussian_map⟩
  have hEach (x : X) :
      (∫D,F (x,D) ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ))=
      ∫w,∫z,F (x,sumJoin (w,z)) ∂δ ∂γ := by
    have hf : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => F (x,sumJoin p)) := by
      simpa only [Function.comp_def] using hF.comp (measurable_const.prodMk sumJoin.continuous.measurable)
    have hi : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => F (x,sumJoin p)) (γ.prod δ) :=
      Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun p => hb _)
    have ht := hS.integral_comp hf.aestronglyMeasurable
    simp only [Function.comp_def,sumJoin_sumSplit] at ht
    exact ht.trans (integral_prod _ hi)
  have hJoint : Measurable (fun p : (X × EuclideanSpace ℝ ι) × EuclideanSpace ℝ κ =>
      F (p.1.1,sumJoin (p.1.2,p.2))) := by
    have hm : Measurable (fun p : (X × EuclideanSpace ℝ ι) × EuclideanSpace ℝ κ =>
        (p.1.1,sumJoin (p.1.2,p.2))) :=
      (measurable_fst.comp measurable_fst).prodMk
        (sumJoin.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    simpa only [Function.comp_def] using hF.comp hm
  have hmInner : Measurable (fun p : X × EuclideanSpace ℝ ι =>
      ∫z,F (p.1,sumJoin (p.2,z)) ∂δ) := hJoint.stronglyMeasurable.integral_prod_right'.measurable
  have hInnerBound (p : X × EuclideanSpace ℝ ι) :
      ‖∫z,F (p.1,sumJoin (p.2,z)) ∂δ‖≤C := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := δ) (f := fun z => F (p.1,sumJoin (p.2,z))) (.of_forall fun z => hb _)
  have hiInner : Integrable (fun p : X × EuclideanSpace ℝ ι =>
      ∫z,F (p.1,sumJoin (p.2,z)) ∂δ) (π.prod γ) :=
    Integrable.of_bound hmInner.aestronglyMeasurable C (.of_forall hInnerBound)
  calc
    _=(∫x,∫w,∫z,F (x,sumJoin (w,z)) ∂δ ∂γ ∂π) := integral_congr_ae (.of_forall hEach)
    _=_ := integral_integral_swap hiInner

end SlowEquilibration.GaussianCompactFeatureComparison
