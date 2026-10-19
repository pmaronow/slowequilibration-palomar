-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairProjectedJetConcentration

/-! Gaussian concentration for actual compact field suprema after an
arbitrary coefficient contraction and the actual posterior mean shift. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianCompactMaximum GaussianNormConcentration
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sourceAffineSupremum {ι κ V:Type*} [Fintype ι] [Fintype κ] (L:V→EuclideanSpace ℝ κ→L[ℝ]ℝ)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ κ) (m:EuclideanSpace ℝ κ)
    (g:EuclideanSpace ℝ ι):ℝ:=⨆ v,L v (T g+m)

theorem sourceAffineSupremum_lipschitz {ι κ V:Type*} [Fintype ι] [Fintype κ] [Nonempty V]
    (L:V→EuclideanSpace ℝ κ→L[ℝ]ℝ) {K:ℝ} (hb:∀ v,‖L v‖ ≤ K)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ κ) (hT:‖T‖ ≤ 1) (m:EuclideanSpace ℝ κ) :
    LipschitzWith K.toNNReal (sourceAffineSupremum L T m):=by
  classical
  have ha:LipschitzWith 1 (fun g=>T g+m):=by
    apply LipschitzWith.of_dist_le_mul
    intro g z
    simp only [NNReal.coe_one,one_mul]
    rw [dist_eq_norm,dist_eq_norm,add_sub_add_right_eq_sub,←map_sub]
    exact (T.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans_eq (one_mul _))
  unfold sourceAffineSupremum
  simpa only [mul_one,Function.comp_def] using
    (field_supremum_lipschitz L hb).comp ha

theorem sourceAffineSupremum_centered_tail {ι κ V:Type*} [Fintype ι] [Fintype κ] [Nonempty V]
    (L:V→EuclideanSpace ℝ κ→L[ℝ]ℝ) {K:ℝ} (hK:0 ≤ K) (hb:∀ v,‖L v‖ ≤ K)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ κ) (hT:‖T‖ ≤ 1) (m:EuclideanSpace ℝ κ)
    {s:ℝ} (hs:0 ≤ s) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g|(∫ z,sourceAffineSupremum L T m z ∂SYK.standardGaussianMeasureOnEuclidean ι)+s ≤
        sourceAffineSupremum L T m g} ≤ Real.exp (-s^2/(2*K^2)):=
  centered_lipschitz_upper_tail _ hK (sourceAffineSupremum_lipschitz L hb T hT m) hs

end
end SlowEquilibration.PairConditionalDeterminantMoments
