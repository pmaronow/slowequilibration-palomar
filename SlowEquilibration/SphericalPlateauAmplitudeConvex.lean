-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeDirections
public import SlowEquilibration.SphericalLogPartitionTilt

@[expose] public section

/-! # Actual finite-volume amplitude convexity

Each true bank amplitude partition follows a single real coefficient line
with the literal planted drift and source penalty absorbed into its actual
sphere Gibbs measure. Convexity follows from the genuine variance theorem.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Metric
open SphericalModel SphericalBarycenter SphericalForm
open SphericalAging.HardSphereDynamics
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The actual finite-volume source amplitude log partition is convex on
the entire real perturbation line, for every realized Gaussian bank. No
pressure limit or stochastic estimate is used. -/
theorem amplitudePartition_line_convex (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (D : BankDisorder n μ) :
    ConvexOn ℝ univ (fun τ : ℝ =>
      Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) D)) := by
  let probe := selectedProbeDisorder p₀ k D
  let P : Vector (n+1) → ℝ := amplitudeField μ x e p₀ (fun _ => 1) probe
  let A : Vector (n+1) → ℝ := fun u => β*amplitudePlantedField μ β x e p₀ (fun _ => 1) D u-
    2*(n+1 : ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)
  have hP : Continuous P := (amplitudeField_contDiff μ x e p₀ (fun _ => 1) probe).continuous
  have hR : Continuous (fun u : Vector (n+1) => overlap x u) := by unfold overlap; fun_prop
  have hA : Continuous A :=
    ((amplitudePlantedField_contDiff μ β x e p₀ (fun _ => 1) D).continuous.const_mul β).sub
      (((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR).const_mul (2*(n+1 : ℝ)))
  let L : Vector (n+1) → EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    fun u => (β*P u) • EuclideanSpace.proj 0
  have hL : Continuous L := (hP.const_mul β).smul continuous_const
  have hLc (w : EuclideanSpace ℝ (Fin 1)) : Continuous (fun u => L u w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp hL)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector (n+1)) (Real.sqrt (n+1 : ℝ))).exists_bound_of_continuousOn
    hL.continuousOn
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  have hb : ∀ u : Vector (n+1), OnSphere u → ‖L u‖ ≤ K := by
    intro u hu
    have hball : u∈closedBall (0 : Vector (n+1)) (Real.sqrt (n+1 : ℝ)) := by
      have hu' : ‖u‖^2=(n : ℝ)+1 := by
        simpa only [Nat.cast_add,Nat.cast_one] using (onSphere_iff_norm_sq u).mp hu
      simp only [mem_closedBall,dist_zero_right]
      rw [← hu',Real.sqrt_sq (norm_nonneg u)]
    exact (hC u hball).trans (le_max_left _ _)
  let d : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hc := spherical_logPartition_line_convex (show 1 ≤ n+1 by omega) hA L hL.measurable hLc
    hK hb (0 : EuclideanSpace ℝ (Fin 1)) d
  have he : (fun τ : ℝ => Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) D))=
      (fun τ => Real.log (partition (n+1) 1 (fun u => A u+L u (0+τ • d)))) := by
    funext τ
    congr 1
    rw [amplitudePartition_at_line]
    unfold partition
    apply integral_congr_ae
    exact .of_forall fun u => by
      dsimp only
      have hLu : L u (0+τ • d)=β*P u*τ := by
        change ((β*P u) • EuclideanSpace.proj (0 : Fin 1)) (0+τ • d)=_
        simp [smul_apply,d,mul_comm]
      rw [one_mul,hLu]
      congr 1
      dsimp only [A,P,probe]
      ring
  rw [he]
  exact hc

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
