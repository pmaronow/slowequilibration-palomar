-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEEdgeConcentration

/-! Actual rank-one Frobenius features for covariance-dominated Gaussian
symmetric matrices. The sharp increment bound compares their quadratic process
with a linear Gaussian process on the unit sphere. -/

@[expose] public section
namespace SlowEquilibration.GaussianMatrixFeatures
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : ℕ}

def rankOneMatrix (u : EuclideanSpace ℝ (Fin m)) : GOEAsymptotics.GaussianMatrix m :=
  WithLp.toLp 2 (fun i => u i • u)

@[simp] lemma rankOneMatrix_apply (u : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    rankOneMatrix u i j = u i * u j := rfl

lemma rankOneMatrix_inner (u v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (rankOneMatrix u) (rankOneMatrix v) = (inner ℝ u v) ^ 2 := by
  change (∑ i, inner ℝ (u i • u) (v i • v)) = (inner ℝ u v)^2
  simp only [inner_smul_left, inner_smul_right, conj_trivial]
  have he : (∑ i : Fin m, u i * v i) = inner ℝ u v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  calc
    _ = (∑ i : Fin m, u i * v i) * inner ℝ u v := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [he]; ring

lemma rankOneMatrix_norm_sq (u : EuclideanSpace ℝ (Fin m)) :
    ‖rankOneMatrix u‖ ^ 2 = ‖u‖ ^ 4 := by
  rw [← real_inner_self_eq_norm_sq, rankOneMatrix_inner, real_inner_self_eq_norm_sq]
  ring

lemma rankOneMatrix_sub_norm_sq (u v : EuclideanSpace ℝ (Fin m)) :
    ‖rankOneMatrix u - rankOneMatrix v‖ ^ 2 =
      ‖u‖ ^ 4 + ‖v‖ ^ 4 - 2 * (inner ℝ u v) ^ 2 := by
  rw [norm_sub_sq_real, rankOneMatrix_norm_sq, rankOneMatrix_norm_sq, rankOneMatrix_inner]
  ring

lemma rankOneMatrix_unit_increment_sq (u v : EuclideanSpace ℝ (Fin m))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖rankOneMatrix u - rankOneMatrix v‖ ^ 2 ≤ 2 * ‖u - v‖ ^ 2 := by
  rw [rankOneMatrix_sub_norm_sq, norm_sub_sq_real, hu, hv]
  nlinarith [sq_nonneg (inner ℝ u v - 1)]

lemma rankOneMatrix_unit_increment (u v : EuclideanSpace ℝ (Fin m))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖rankOneMatrix u - rankOneMatrix v‖ ≤ Real.sqrt 2 * ‖u - v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact rankOneMatrix_unit_increment_sq u v hu hv

lemma rankOneMatrix_continuous : Continuous (rankOneMatrix (m := m)) := by
  unfold rankOneMatrix
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => (PiLp.continuous_apply 2 _ i).smul continuous_id)

lemma quadratic_eq_rankOne_inner (A : GOEAsymptotics.GaussianMatrix m)
    (u : EuclideanSpace ℝ (Fin m)) :
    inner ℝ u (gaussianMatrixCLM A u) = inner ℝ (rankOneMatrix u) A := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i, (∑ j, A i j * u j) * u i) = ∑ i, ∑ j, A i j * (u i * u j)
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine Gaussian coefficient vector of the quadratic field. -/
def quadraticFeature (W : E →L[ℝ] GOEAsymptotics.GaussianMatrix m)
    (u : EuclideanSpace ℝ (Fin m)) : E := W.adjoint (rankOneMatrix u)

lemma quadraticFeature_apply (W : E →L[ℝ] GOEAsymptotics.GaussianMatrix m)
    (u : EuclideanSpace ℝ (Fin m)) (g : E) :
    inner ℝ (quadraticFeature W u) g = inner ℝ u (gaussianMatrixCLM (W g) u) := by
  rw [quadratic_eq_rankOne_inner, quadraticFeature, ContinuousLinearMap.adjoint_inner_left]

lemma quadraticFeature_unit_increment (W : E →L[ℝ] GOEAsymptotics.GaussianMatrix m)
    {σ : ℝ} (hσ : 0 ≤ σ) (hW : ‖W‖ ≤ σ)
    (u v : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖quadraticFeature W u - quadraticFeature W v‖ ≤ (Real.sqrt 2 * σ) * ‖u-v‖ := by
  unfold quadraticFeature
  rw [← W.adjoint.map_sub]
  calc
    _ ≤ ‖W.adjoint‖ * ‖rankOneMatrix u - rankOneMatrix v‖ := W.adjoint.le_opNorm _
    _ ≤ σ * (Real.sqrt 2 * ‖u-v‖) :=
      mul_le_mul (by rw [ContinuousLinearMap.adjoint.norm_map]; exact hW) (rankOneMatrix_unit_increment u v hu hv) (norm_nonneg _) hσ
    _ = _ := by ring

end
end SlowEquilibration.GaussianMatrixFeatures
