-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudePressureLaw
public import SlowEquilibration.SphericalPlateauAmplitudeConvex

@[expose] public section

/-! # Actual amplitude log-partition integrability and expected-pressure convexity

Every finite physical amplitude is integrated against the genuine Gaussian
bank. The entire perturbation line is convex after taking the actual expectation.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The actual compact log-partition observable grows at most linearly in
its random continuous field, with its deterministic penalty retained. -/
theorem weightedLogPartitionFunctional_norm_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (f : C(CompactSphereCarrier.Carrier (n+1),ℝ)) :
    ‖weightedLogPartitionFunctional μ β J δ q₁ q₂ x f‖≤
      |β| *‖f‖+‖weightedLogPartitionFunctional μ β J δ q₁ q₂ x 0‖ := by
  let := CompactSphereCarrier.law_probability (by omega : 1≤n+1)
  have h := (ContinuousFieldPartition.logPartition_lipschitz
    (CompactSphereCarrier.law (n+1)) 1).norm_sub_le
      (β • f+plantedPenaltyMap μ β J δ q₁ q₂ x)
      (β • (0:C(CompactSphereCarrier.Carrier (n+1),ℝ))+plantedPenaltyMap μ β J δ q₁ q₂ x)
  simp only [abs_one,smul_zero,zero_add,
    add_sub_cancel_right,norm_smul,Real.norm_eq_abs] at h
  have hh : ‖weightedLogPartitionFunctional μ β J δ q₁ q₂ x f-
      weightedLogPartitionFunctional μ β J δ q₁ q₂ x 0‖≤|β| *‖f‖ := by
    change _ ≤ (1:ℝ)*(|β| *‖f‖) at h
    rw [one_mul] at h
    simpa only [weightedLogPartitionFunctional,smul_zero,zero_add,Real.norm_eq_abs] using h
  calc
    _ = ‖(weightedLogPartitionFunctional μ β J δ q₁ q₂ x f-
      weightedLogPartitionFunctional μ β J δ q₁ q₂ x 0)+weightedLogPartitionFunctional μ β J δ q₁ q₂ x 0‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hh le_rfl)

/-- Every actual bank amplitude log partition is integrable. This holds at
all perturbation parameters without a pressure estimate. -/
theorem amplitudePartition_log_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) : Integrable (fun D : BankDisorder n μ =>
      Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ s D)) (bankLaw n μ) := by
  let L := bankContinuousField μ x e p₀ s
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val
  let F := weightedLogPartitionFunctional μ β J δ q₁ q₂ x
  have hF : Measurable F := weightedLogPartitionFunctional_measurable μ β J δ q₁ q₂ x
  have hnorm : Integrable (fun w : EuclideanBank n μ => ‖w‖) (stdGaussian (EuclideanBank n μ)) :=
    (IsGaussian.integrable_id (μ := stdGaussian (EuclideanBank n μ))).norm
  have hdom : Integrable (fun w : EuclideanBank n μ => |β| *‖L‖*‖w‖+‖F 0‖)
      (stdGaussian (EuclideanBank n μ)) := (hnorm.const_mul _).add (integrable_const _)
  have hi : Integrable (fun w : EuclideanBank n μ => F (L w)) (stdGaussian (EuclideanBank n μ)) := by
    apply hdom.mono' (hF.comp L.continuous.measurable).aestronglyMeasurable
    exact .of_forall fun w =>
      (weightedLogPartitionFunctional_norm_le μ β J δ q₁ q₂ x (L w)).trans
        (add_le_add (by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (L.le_opNorm w) (abs_nonneg β)) le_rfl)
  have hcomp := (actual_bank_flattened_gaussian n μ).integrable_comp hi
  have he : (fun D : BankDisorder n μ => F (L (euclideanBank D)))=
      fun D => Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ s D) := by
    funext D
    exact weightedLogPartitionFunctional_bank μ β J δ q₁ q₂ x e p₀ s D
  change Integrable (fun D => F (L (euclideanBank D))) (bankLaw n μ) at hcomp
  rwa [he] at hcomp

/-- The literal quenched expected pressure is convex along every actual
source transverse amplitude line, on the whole real line. -/
theorem amplitudeExpectedPressure_line_convex (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) : ConvexOn ℝ univ (fun τ : ℝ =>
      amplitudeExpectedPressure μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ)) := by
  refine ⟨convex_univ,?_⟩
  intro a ha b hb u v hu hv huv
  have hi (τ : ℝ) := amplitudePartition_log_integrable μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ)
  have hpoint (D : BankDisorder n μ) :=
    (amplitudePartition_line_convex μ β J δ q₁ q₂ x e p₀ k D).2 ha hb hu hv huv
  simp only [smul_eq_mul] at hpoint ⊢
  have hInt := integral_mono (hi (u*a+v*b)) (((hi a).const_mul u).add ((hi b).const_mul v)) hpoint
  dsimp only [Pi.add_apply] at hInt
  rw [integral_add ((hi a).const_mul u) ((hi b).const_mul v),integral_const_mul,integral_const_mul] at hInt
  have hNp : 0<(n+1:ℝ) := by positivity
  have hh := div_le_div_of_nonneg_right hInt hNp.le
  unfold amplitudeExpectedPressure
  convert hh using 1
  ring

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
