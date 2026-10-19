-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSelectedReplicaTrace
public import SlowEquilibration.SphericalGaussianInterpolation

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeKernel

open SphericalModel GaussianSpinInterpolation GaussianSpinComparison
open GaussianSelectedReplicaTrace
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def activeDegreeLabel {N P : ℕ} (p : Degree P) (i : Coordinate N P) : Bool :=
  decide (i.1 = p)

def activeDegreeLinear {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Vector N → EuclideanDisorder N P →L[ℝ] ℝ :=
  scaledLinear (sphereLinear c) β

theorem activeDegree_coordinate {N P : ℕ} (c : Degree P → ℝ)
    (β : ℝ) (i : Coordinate N P) (x : Vector N) :
    coordinateObservable (activeDegreeLinear c β) i x =
      β * fieldFeature c x i := by
  simp only [activeDegreeLinear,scaledLinear,coordinateObservable,
    smul_apply,smul_eq_mul,sphereLinear_coordinate]

theorem activeDegree_selectedKernel {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (p : Degree P) (x y : Vector N) :
    selectedKernel (activeDegreeLinear c β) (activeDegreeLabel (N := N) p) x y =
      β^2*(c p)*(N : ℝ)*(overlap x y)^p.val.val := by
  unfold selectedKernel selectedWeight activeDegreeLabel
  simp_rw [activeDegree_coordinate, Fintype.sum_sigma]
  simp only [decide_eq_true_eq]
  simp only [ite_mul, one_mul, zero_mul]
  calc
    _ = ∑ q : Degree P, if q = p then
          ∑ I : SphericalAging.FiniteModel.TensorIndex N q.val.val,
            β * fieldFeature c x ⟨q,I⟩ * (β * fieldFeature c y ⟨q,I⟩)
          else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs with h <;> simp
    _ = _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [fieldFeature]
      have hsqrt := Real.sq_sqrt (hc p)
      have hscale := SphericalAging.FiniteModel.dimension_covariance_scale
        N p.val.val (lt_of_lt_of_le Nat.zero_lt_one hN)
          (by omega : 1 ≤ p.val.val) (inner ℝ x y)
      rw [← SphericalAging.FiniteModel.normalization_sq N p.val.val
        (lt_of_lt_of_le Nat.zero_lt_one hN)] at hscale
      calc
        _ = β^2 * (Real.sqrt (c p))^2 *
            SphericalAging.FiniteModel.normalization N p.val.val^2 *
            ∑ I, SphericalAging.FiniteModel.tensorMonomial x I *
              SphericalAging.FiniteModel.tensorMonomial y I := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro I _
          ring
        _ = β^2 * c p *
            (SphericalAging.FiniteModel.normalization N p.val.val^2 *
              (inner ℝ x y)^p.val.val) := by
          rw [hsqrt, SphericalAging.FiniteModel.tensorMonomial_gram]
          ring
        _ = _ := by rw [hscale]; simp only [overlap]; ring

end SlowEquilibration.SphericalActiveDegreeKernel
