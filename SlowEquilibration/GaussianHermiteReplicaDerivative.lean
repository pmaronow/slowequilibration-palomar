-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianHermiteMixedDerivative
public import SlowEquilibration.GaussianReplicaDerivatives

/-! The Hermite mixed derivatives and the Gibbs replica derivatives use the
same ordered coordinate directions. Their equality connects smooth
integration by parts to the actual replica differentiation formula. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianHermiteDerivative

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open GaussianSpinInterpolation GaussianReplicaDerivatives
open scoped NNReal

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]

/-- Repeated directional derivatives commute with a fixed continuous
linear pullback, with every direction mapped by that same map. -/
theorem directionalDerivatives_comp_clm
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : H → ℝ) (A : E →L[ℝ] H)
    (hF : ∀ n d, Differentiable ℝ (directionalDerivatives F n d))
    (n : ℕ) (d : Fin n → E) :
    directionalDerivatives (fun x => F (A x)) n d =
      fun x => directionalDerivatives F n (fun k => A (d k)) (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun x => fderiv ℝ
      (directionalDerivatives (fun y => F (A y)) n (fun k => d k.castSucc)) x
        (d (Fin.last n))) = _
    rw [ih]
    funext x
    have hc := ((hF n (fun k => A (d k.castSucc)) (A x)).hasFDerivAt).comp x
      A.hasFDerivAt
    have hd := hc.fderiv
    simp only [Function.comp_def] at hd
    rw [hd]
    rfl

theorem mixedCoordinatePartial_eq_directionalDerivatives
    (f : (ι → ℝ) → ℝ) (n : ℕ) (d : Fin n → ι) :
    mixedCoordinatePartial f n d =
      directionalDerivatives f n (fun k => Pi.single (d k) 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mixedCoordinatePartial, directionalDerivatives, ih, coordinatePartial]
    rfl

/-- The product-coordinate Hermite derivatives are precisely the
Euclidean directional derivatives used by the physical coefficient model. -/
theorem mixedCoordinatePartial_euclidean_pullback
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ∀ n d, Differentiable ℝ (directionalDerivatives F n d))
    (n : ℕ) (d : Fin n → ι) (x : ι → ℝ) :
    mixedCoordinatePartial (fun y => F (WithLp.toLp 2 y)) n d x =
      directionalDerivatives F n (fun k => EuclideanSpace.single (d k) 1)
        (WithLp.toLp 2 x) := by
  rw [mixedCoordinatePartial_eq_directionalDerivatives]
  let A : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
  have hh := congrFun (directionalDerivatives_comp_clm F A hF n
    (fun k => Pi.single (d k) 1)) x
  simpa only [A, ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_single, EuclideanSpace.single] using hh

theorem integral_mixedCoordinatePartial_euclidean_pullback
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ∀ n d, Differentiable ℝ (directionalDerivatives F n d))
    (n : ℕ) (d : Fin n → ι) :
    (∫ x, mixedCoordinatePartial (fun y => F (WithLp.toLp 2 y)) n d x ∂γpi ι) =
      ∫ w, directionalDerivatives F n (fun k => EuclideanSpace.single (d k) 1) w
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  rw [SYK.standardGaussianMeasureOnEuclidean,
    integral_map (WithLp.measurable_toLp 2 _).aemeasurable
      ((hF n _).continuous.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mixedCoordinatePartial_euclidean_pullback F hF n d x

/-- Smoothness and Lipschitz bounds for the genuine Euclidean derivatives
give every growth bound needed for the product-coordinate Hermite proof. -/
theorem mixedCoordinatePartial_euclidean_pullback_exponentialFirstJet
    (F : EuclideanSpace ℝ ι → ℝ)
    (hFC : ∀ n d, ContDiff ℝ 1 (directionalDerivatives F n d))
    (hFL : ∀ n d, ∃ B : ℝ≥0, LipschitzWith B (directionalDerivatives F n d))
    (n : ℕ) (d : Fin n → ι) :
    ExponentialFirstJet (mixedCoordinatePartial (fun y => F (WithLp.toLp 2 y)) n d) := by
  have heq : mixedCoordinatePartial (fun y => F (WithLp.toLp 2 y)) n d =
      fun x => directionalDerivatives F n (fun k => EuclideanSpace.single (d k) 1)
        (WithLp.toLp 2 x) := by
    funext x
    exact mixedCoordinatePartial_euclidean_pullback F
      (fun n d => (hFC n d).differentiable (by norm_num)) n d x
  rw [heq]
  let A : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
  obtain ⟨B, hB⟩ := hFL n (fun k => EuclideanSpace.single (d k) 1)
  exact ExponentialFirstJet.of_lipschitz _ ((hFC n _).comp A.contDiff)
    (B * ‖A‖₊) (hB.comp A.lipschitz)

/-- Every actual repeated coordinate derivative of a bounded-feature log
partition satisfies the smooth growth condition required by Hermite IBP. -/
theorem mixedCoordinatePartial_logPartition_exponentialFirstJet
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → (ι → ℝ) →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin n → ι) :
    ExponentialFirstJet (mixedCoordinatePartial (logPartition ν L) n d) := by
  rw [mixedCoordinatePartial_eq_directionalDerivatives]
  obtain ⟨B, hB⟩ := directionalDerivatives_logPartition_lipschitz ν L hL hK hb n
    (fun k => Pi.single (d k) 1)
  exact ExponentialFirstJet.of_lipschitz _
    (directionalDerivatives_logPartition_contDiff ν L hL hK hb n _) B hB

theorem mixedCoordinatePartial_logPartition_memLp_two
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → (ι → ℝ) →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin n → ι) :
    MemLp (mixedCoordinatePartial (logPartition ν L) n d) 2 (γpi ι) :=
  (mixedCoordinatePartial_logPartition_exponentialFirstJet ν L hL hK hb n d).memLp_two

/-- For a genuine bounded-feature Gibbs log partition, the mean of an
ordered derivative equals its chaos coefficient with the exact factorial
normalization. Smoothness and all integrability are discharged here. -/
theorem integral_logPartition_mixedDerivative_square
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → (ι → ℝ) →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin n → ι) :
    (∫ x, mixedCoordinatePartial (logPartition ν L) n d x ∂γpi ι) ^ 2 =
      factorialProduct (raisedIndex n d 0) *
        (coeff (logPartition ν L) (raisedIndex n d 0)) ^ 2 := by
  exact integral_mixedCoordinatePartial_square (logPartition ν L)
    (mixedCoordinatePartial_logPartition_exponentialFirstJet ν L hL hK hb)
    (mixedCoordinatePartial_logPartition_memLp_two ν L hL hK hb) n d

end SlowEquilibration.GaussianHermiteDerivative
