-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureSmoothCutoff
public import SlowEquilibration.ConditionedEntranceSourceCutoffInterior

/-! The proper pure cutoff Hamiltonian has the exact value/tangent-posterior
gradient on the interior of its two physical cutoff coordinates. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalPosteriorMaps WholeFieldRegression
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem pureSourceSmoothCutoffField_eq_one_inside
    {N : ℕ} (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (x : Vector N)
    (hr : |overlap x u / α| ≤ 1)
    (hs : |inner ℝ (surfaceGradient
      (field (centerCoefficients
        (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) J) u) x /
        ((N : ℝ) * α)| ≤ 1) :
    pureSourceSmoothCutoffField p hp c hc Q J u e α sourceScalarCutoff x =
      pureSourceSmoothCutoffField p hp c hc Q J u e α (fun _ => 1) x := by
  simp only [pureSourceSmoothCutoffField, sourceScalarCutoff_eq_one hr,
    sourceScalarCutoff_eq_one hs, one_mul]

theorem pureSourceSmoothCutoffField_gradient_eq_actual_valuePosterior_inside
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (e α : ℝ) (x : Vector (n+1))
    (hr : |overlap x u / α| < 1)
    (hs : |inner ℝ (surfaceGradient
      (field (centerCoefficients
        (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q)
        (unpackDisorder g)) u) x / (((n+1 : ℕ) : ℝ) * α)| < 1) :
    gradient (pureSourceSmoothCutoffField p hp c hc Q (unpackDisorder g)
      u e α sourceScalarCutoff) x =
      gradient (fieldOfMixture (FiniteMixture.pure p hp c hc)
        (unpackDisorder (valuePosterior n (FiniteMixture.pure p hp c hc)
          Q u e g))) x := by
  let μ := FiniteMixture.pure p hp c hc
  let J := unpackDisorder g
  let R : Vector (n+1) → ℝ := fun y => overlap y u / α
  let S : Vector (n+1) → ℝ := fun y => inner ℝ (surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) y /
        (((n+1 : ℕ) : ℝ) * α)
  have hRc : Continuous R := by dsimp only [R,overlap]; fun_prop
  have hSc : Continuous S := by dsimp only [S]; fun_prop
  have heR : ∀ᶠ y in nhds x, |R y| < 1 :=
    hRc.abs.continuousAt.eventually_lt continuousAt_const hr
  have heS : ∀ᶠ y in nhds x, |S y| < 1 :=
    hSc.abs.continuousAt.eventually_lt continuousAt_const hs
  have heq :
      (pureSourceSmoothCutoffField p hp c hc Q J u e α sourceScalarCutoff) =ᶠ[nhds x]
      (pureSourceSmoothCutoffField p hp c hc Q J u e α (fun _ => 1)) := by
    filter_upwards [heR,heS] with y hy hz
    exact pureSourceSmoothCutoffField_eq_one_inside
      p hp c hc Q J u e α y hy.le hz.le
  have hdcut : DifferentiableAt ℝ
      (pureSourceSmoothCutoffField p hp c hc Q J u e α sourceScalarCutoff) x :=
    (pureSourceSmoothCutoffField_contDiff (by omega : 1 ≤ n+1)
      p hp c hc Q J u e α sourceScalarCutoff
      sourceScalarCutoff_contDiff_two).differentiable (by norm_num) x
  have hdone : DifferentiableAt ℝ
      (pureSourceSmoothCutoffField p hp c hc Q J u e α (fun _ => 1)) x :=
    (pureSourceSmoothCutoffField_contDiff (by omega : 1 ≤ n+1)
      p hp c hc Q J u e α (fun _ => 1)
      contDiff_const).differentiable (by norm_num) x
  have hgrad := hdcut.hasGradientAt.unique
    (hdone.hasGradientAt.congr_of_eventuallyEq heq)
  have hfun :
      pureSourceSmoothCutoffField p hp c hc Q J u e α (fun _ => 1) =
      fieldOfMixture μ (unpackDisorder (valuePosterior n μ Q u e g)) := by
    funext y
    exact pureSourceSmoothCutoffField_one_eq_actual_posterior
      n p hp c hc hQ u hu e α g y
  rw [← hfun]
  exact hgrad

end SlowEquilibration.ConditionedEntrance
