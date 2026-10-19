-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntrancePureAxisCapHit
public import SlowEquilibration.ConditionedEntranceSourceFieldRotation
public import SlowEquilibration.SphericalSmoothCapHitRotation

/-! Orthogonal covariance of the proper pure source correction, its
cutoff Hamiltonian, and the actual finite-horizon cap-hit probability. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureAxisRotation

open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalRotationCovariance
open SphericalSmoothParameter SphericalAging.HardSphereDynamics ConditionedEntrance
open scoped NNReal RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {N : ℕ}

theorem pureSourceRegressionCorrection_rotated
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u x : Vector N) (e : ℝ) :
    pureSourceRegressionCorrection p hp c hc Q (rotatedDisorder U J) (U u) e (U x) =
      pureSourceRegressionCorrection p hp c hc Q J u e x := by
  unfold pureSourceRegressionCorrection pureRegressionCorrection
  rw [sourceCenterGradient_rotated (FiniteMixture.pure p hp c hc) Q U J u,field_rotated]
  simp only [overlap,U.inner_map_map]

theorem pureSourceSmoothCutoffField_rotated
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u x : Vector N) (e α : ℝ) (χ : ℝ → ℝ) :
    pureSourceSmoothCutoffField p hp c hc Q (rotatedDisorder U J) (U u) e α χ (U x) =
    pureSourceSmoothCutoffField p hp c hc Q J u e α χ x := by
  unfold pureSourceSmoothCutoffField
  dsimp only
  rw [pureSourceRegressionCorrection_rotated p hp c hc Q U J u x e,
    sourceCenterGradient_rotated (FiniteMixture.pure p hp c hc) Q U J u]
  dsimp only [fieldOfMixture]
  rw [field_rotated]
  simp only [overlap,U.inner_map_map]

theorem pureSourceSmoothCutoffGradient_rotated (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u x : Vector N) (e α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    gradient (pureSourceSmoothCutoffField p hp c hc Q (rotatedDisorder U J)
      (U u) e α χ) (U x) =
      U (gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) x) := by
  let H := pureSourceSmoothCutoffField p hp c hc Q J u e α χ
  have heq : pureSourceSmoothCutoffField p hp c hc Q (rotatedDisorder U J)
      (U u) e α χ = fun y => H (U.symm y) := by
    funext y
    simpa only [H,U.apply_symm_apply] using
      pureSourceSmoothCutoffField_rotated p hp c hc Q U J u (U.symm y) e α χ
  have hf : Differentiable ℝ H :=
    (pureSourceSmoothCutoffField_contDiff hN p hp c hc Q J u e α χ hχ).differentiable
      (by norm_num)
  rw [heq,gradient_comp_rotation U.symm hf (U x)]
  simp [H]

theorem pureAxisCapHitProbability_rotated (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (T : ℝ≥0) (u x : Vector N) (hx : OnSphere x) :
    pureAxisCapHitProbability p hp c hc Q (rotatedDisorder U J)
      β α χ hχ e T (U u) (U x) =
      pureAxisCapHitProbability p hp c hc Q J β α χ hχ e T u x := by
  let g := jointSpatialGradient (fun z : Vector N × Vector N =>
    pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2)
  let g' := jointSpatialGradient (fun z : Vector N × Vector N =>
    pureSourceSmoothCutoffField p hp c hc Q (rotatedDisorder U J) z.1 e α χ z.2)
  have hg : ContDiff ℝ 1 g := pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e
  have hg' : ContDiff ℝ 1 g' :=
    pure_axisJointGradient_contDiff p hp c hc Q α χ hχ (rotatedDisorder U J) e
  have hgrad (v : Vector N) : g' (U u,U v) = U (g (u,v)) := by
    change gradient (pureSourceSmoothCutoffField p hp c hc Q (rotatedDisorder U J)
      (U u) e α χ) (U v) =
      U (gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) v)
    exact pureSourceSmoothCutoffGradient_rotated hN p hp c hc Q U J u v e α χ hχ
  change capHitProbability β g' hg' T (α/2) (U u,(U u,U x)) =
    capHitProbability β g hg T (α/2) (u,(u,x))
  exact capHitProbability_rotation_at (by omega : N ≠ 0) U β g hg g' hg'
    u (U u) hgrad u x hx T (α/2)

end SlowEquilibration.SourceConditionedCPTransferPureAxisRotation
