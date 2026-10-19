-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaDerivatives
public import SlowEquilibration.SphericalGaussianInterpolation
public import SlowEquilibration.IndependentReplicaTensorContraction

/-! Exact physical coefficient factors in a fixed Gibbs derivative.
The scalar temperature, mixture amplitudes and powers of N are kept outside
the unnormalized replicated spin monomial.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalTensorDerivativeNormalization

open MeasureTheory ProbabilityTheory
open SphericalModel GaussianSpinInterpolation GaussianReplicaDerivatives
open IndependentReplicaTensorContraction
open scoped BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The derivative of the physical linear field in one actual ordered
tensor coefficient. -/
theorem sphereLinear_coordinate {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (x : Vector N) (p : Degree P) (I : SphericalAging.FiniteModel.TensorIndex N p.val.val) :
    scaledLinear (sphereLinear c) β x (EuclideanSpace.single ⟨p, I⟩ 1) =
      (β * Real.sqrt (c p) * SphericalAging.FiniteModel.normalization N p.val.val) *
        SphericalAging.FiniteModel.tensorMonomial x I := by
  simp only [scaledLinear, smul_apply, smul_eq_mul, sphereLinear,
    innerSL_apply_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial, fieldFeature]
  ring

/-- All physical tensor slots in one fixed sequence of derivative degrees. -/
abbrev TensorSlots {k P : ℕ} (p : Fin k → Degree P) :=
  (j : Fin k) × Fin (p j).val.val

def totalTensorDegree {k P : ℕ} (p : Fin k → Degree P) : ℕ := ∑ j, (p j).val.val

theorem card_tensorSlots {k P : ℕ} (p : Fin k → Degree P) :
    Fintype.card (TensorSlots p) = totalTensorDegree p := by
  simp [TensorSlots, totalTensorDegree, Fintype.card_sigma]

instance tensorSlots_nonempty {k P : ℕ} [NeZero k] (p : Fin k → Degree P) :
    Nonempty (TensorSlots p) := by
  let j : Fin k := ⟨0, Nat.pos_of_neZero k⟩
  exact ⟨⟨j, ⟨0, by have := (p j).property; omega⟩⟩⟩

def tensorDerivativeAmplitude (N : ℕ) {k P : ℕ} (c : Degree P → ℝ)
    (β : ℝ) (p : Fin k → Degree P) : ℝ :=
  ∏ j, β * Real.sqrt (c (p j)) * SphericalAging.FiniteModel.normalization N (p j).val.val

def flattenedTensorIndex {N k P : ℕ} (p : Fin k → Degree P)
    (I : (j : Fin k) → SphericalAging.FiniteModel.TensorIndex N (p j).val.val) :
    TensorSlots p → Fin N := fun a => I a.1 a.2

def flattenedReplicaLabels {k P r : ℕ} (p : Fin k → Degree P)
    (labels : Fin k → Fin r) : TensorSlots p → Fin r := fun a => labels a.1

/-- Each feature monomial has exactly its physical scalar amplitude times
one unrestricted ordered replicated spin monomial. -/
theorem featureMonomial_eq_amplitude_mul_replicaMonomial {N k P r : ℕ}
    (c : Degree P → ℝ) (β : ℝ) (p : Fin k → Degree P)
    (I : (j : Fin k) → SphericalAging.FiniteModel.TensorIndex N (p j).val.val)
    (labels : Fin k → Fin r) (σ : Fin r → Vector N) :
    featureMonomial (scaledLinear (sphereLinear c) β) labels
      (fun j => EuclideanSpace.single ⟨p j, I j⟩ 1) σ =
    tensorDerivativeAmplitude N c β p *
      replicaMonomial (flattenedReplicaLabels p labels) (fun a i => σ a i)
        (flattenedTensorIndex p I) := by
  simp only [featureMonomial, sphereLinear_coordinate, tensorDerivativeAmplitude,
    replicaMonomial, flattenedReplicaLabels, flattenedTensorIndex,
    SphericalAging.FiniteModel.tensorMonomial, Fintype.prod_sigma,
    Finset.prod_mul_distrib]

/-- Degrees at least two give at least two physical tensor slots for each
disorder derivative; no parity assumption occurs. -/
theorem twice_order_le_totalTensorDegree {k P : ℕ} (p : Fin k → Degree P) :
    2 * k ≤ totalTensorDegree p := by
  calc
    _ = ∑ _j : Fin k, 2 := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun j _ => (p j).property

/-- Exact squared physical normalization for a fixed derivative-degree
sequence.  The remaining amplitude is independent of the dimension. -/
theorem tensorDerivativeAmplitude_sq {N k P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (p : Fin k → Degree P) :
    tensorDerivativeAmplitude N c β p ^ 2 =
      (∏ j, β ^ 2 * c (p j)) *
        (N : ℝ) ^ (-((totalTensorDegree p - k : ℕ) : ℝ)) := by
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn (j : Fin k) : SphericalAging.FiniteModel.normalization N (p j).val.val ^ 2 =
      (N : ℝ) ^ (-(((p j).val.val - 1 : ℕ) : ℝ)) := by
    unfold SphericalAging.FiniteModel.normalization
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    push_cast
    ring
  have hp (j : Fin k) :
      (β * Real.sqrt (c (p j)) * SphericalAging.FiniteModel.normalization N (p j).val.val) ^ 2 =
        (β ^ 2 * c (p j)) * (N : ℝ) ^ (-(((p j).val.val - 1 : ℕ) : ℝ)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (hc _), hn]
  have hs : (∑ j : Fin k, ((p j).val.val - 1)) = totalTensorDegree p - k := by
    rw [Finset.sum_tsub_distrib _ (fun j _ => by have := (p j).property; omega)]
    simp [totalTensorDegree]
  unfold tensorDerivativeAmplitude
  rw [← Finset.prod_pow]
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Real.rpow_sum_of_pos hNp]
  congr 1
  rw [Finset.sum_neg_distrib, ← Nat.cast_sum, hs]

end SlowEquilibration.SphericalTensorDerivativeNormalization
