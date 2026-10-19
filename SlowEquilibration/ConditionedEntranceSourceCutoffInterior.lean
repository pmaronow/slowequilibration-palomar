-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceActualCutoff
public import SlowEquilibration.ConditionedEntranceSmoothStationarity
public import SlowEquilibration.SphericalOriginalPosteriorSourceField

/-! The source's two physical cutoff coordinates are compared with the
uncut Gaussian-regression posterior in the interior where both cutoffs
equal one. This is the deterministic field equality used before applying
local pathwise uniqueness in the final entrance coupling. -/
@[expose] public section
noncomputable section
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.EntranceSmoothCutoffTensorApproximation
open scoped RealInnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000

/-- For the actual center-gradient coordinate, the literal smooth
source Hamiltonian equals the untruncated regression field throughout
the closed interior of both cutoffs. -/
theorem sourceSmoothCutoffField_eq_uncut_inside
    {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (u : Vector N) (e k α : ℝ)
    (x : Vector N)
    (hr : |overlap x u / α| ≤ 1)
    (hs : |inner ℝ (surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) x /
        ((N : ℝ) * α)| ≤ 1) :
    sourceSmoothCutoffField μ Q hQ hnp J u e k α sourceScalarCutoff x =
      fieldOfMixture μ J x +
        sourceRegressionCorrection μ Q hQ hnp J u e k x := by
  rw [sourceSmoothCutoffField_eq]
  rw [sourceScalarCutoff_eq_one hr, sourceScalarCutoff_eq_one hs]
  ring

/-- The same equality, now identifying the untruncated field with the
actual mixed Gaussian-regression posterior built from the original
coefficient seed. There is no replacement conditioned-field assumption. -/
theorem sourceSmoothCutoffField_eq_actual_mixedPosterior_inside
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (g : EuclideanDisorder (n+1) μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e k α : ℝ) (x : Vector (n+1))
    (hr : |overlap x u / α| ≤ 1)
    (hs : |inner ℝ (surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder g)) u) x / (((n+1 : ℕ) : ℝ) * α)| ≤ 1) :
    sourceSmoothCutoffField μ Q hQ hnp (unpackDisorder g) u e k α
      sourceScalarCutoff x =
      fieldOfMixture μ (unpackDisorder
        (SphericalPosteriorMaps.mixedPosterior n μ Q u
          (SphericalMarkedWindows.scorePairEquiv (e,k)) g)) x := by
  rw [sourceSmoothCutoffField_eq_uncut_inside μ Q hQ hnp
    (unpackDisorder g) u e k α x hr hs]
  exact (SphericalCriticalLatitude.actual_mixedPosterior_original_field
    n μ hQ hnp u hu e k g x).symm

/-- On the strict interior the two actual ambient gradients agree. This
is the drift identity needed to localize physical pathwise uniqueness. -/
theorem sourceSmoothCutoffField_gradient_eq_uncut_inside
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (Q : ℝ) (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (u : Vector N) (e k α : ℝ)
    (x : Vector N)
    (hr : |overlap x u / α| < 1)
    (hs : |inner ℝ (surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) x /
        ((N : ℝ) * α)| < 1) :
    gradient (sourceSmoothCutoffField μ Q hQ hnp J u e k α sourceScalarCutoff) x =
      gradient (fun y => fieldOfMixture μ J y +
        sourceRegressionCorrection μ Q hQ hnp J u e k y) x := by
  let R : Vector N → ℝ := fun y => overlap y u / α
  let S : Vector N → ℝ := fun y => inner ℝ (surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) y /
        ((N : ℝ) * α)
  have hRc : Continuous R := by
    dsimp only [R,overlap]
    fun_prop
  have hSc : Continuous S := by
    dsimp only [S]
    fun_prop
  have heR : ∀ᶠ y in nhds x, |R y| < 1 :=
    hRc.abs.continuousAt.eventually_lt continuousAt_const hr
  have heS : ∀ᶠ y in nhds x, |S y| < 1 :=
    hSc.abs.continuousAt.eventually_lt continuousAt_const hs
  have heq :
      (sourceSmoothCutoffField μ Q hQ hnp J u e k α sourceScalarCutoff) =ᶠ[nhds x]
        (fun y => fieldOfMixture μ J y +
          sourceRegressionCorrection μ Q hQ hnp J u e k y) := by
    filter_upwards [heR,heS] with y hy hz
    exact sourceSmoothCutoffField_eq_uncut_inside μ Q hQ hnp J u e k α y hy.le hz.le
  have hdreg : DifferentiableAt ℝ
      (sourceRegressionCorrection μ Q hQ hnp J u e k) x := by
    exact (regressionCorrection_contDiff hN μ Q u
      (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u)
      (field (centerCoefficients (mixtureCoefficients μ) Q) J u)
      (jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u (fun _ => u) J)
      e k).differentiable (by norm_num) x
  have hduncut : DifferentiableAt ℝ
      (fun y => fieldOfMixture μ J y +
        sourceRegressionCorrection μ Q hQ hnp J u e k y) x :=
    ((fieldOfMixture_contDiff μ J).differentiable (by norm_num) x).add hdreg
  have hdcut : DifferentiableAt ℝ
      (sourceSmoothCutoffField μ Q hQ hnp J u e k α sourceScalarCutoff) x :=
    (sourceSmoothCutoffField_contDiff hN μ Q hQ hnp J u e k α
      sourceScalarCutoff sourceScalarCutoff_contDiff_two).differentiable (by norm_num) x
  exact (hdcut.hasGradientAt.unique
    (hduncut.hasGradientAt.congr_of_eventuallyEq heq))

/-- The source cutoff drift is exactly the actual mixed posterior drift
on the strict two-coordinate interior. -/
theorem sourceSmoothCutoffField_gradient_eq_actual_mixedPosterior_inside
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (g : EuclideanDisorder (n+1) μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e k α : ℝ) (x : Vector (n+1))
    (hr : |overlap x u / α| < 1)
    (hs : |inner ℝ (surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder g)) u) x / (((n+1 : ℕ) : ℝ) * α)| < 1) :
    gradient (sourceSmoothCutoffField μ Q hQ hnp (unpackDisorder g)
      u e k α sourceScalarCutoff) x =
      gradient (fieldOfMixture μ (unpackDisorder
        (SphericalPosteriorMaps.mixedPosterior n μ Q u
          (SphericalMarkedWindows.scorePairEquiv (e,k)) g))) x := by
  have hfun : (fun y : Vector (n+1) =>
      fieldOfMixture μ (unpackDisorder g) y +
        sourceRegressionCorrection μ Q hQ hnp (unpackDisorder g) u e k y) =
      fieldOfMixture μ (unpackDisorder
        (SphericalPosteriorMaps.mixedPosterior n μ Q u
          (SphericalMarkedWindows.scorePairEquiv (e,k)) g)) := by
    funext y
    exact (SphericalCriticalLatitude.actual_mixedPosterior_original_field
      n μ hQ hnp u hu e k g y).symm
  rw [sourceSmoothCutoffField_gradient_eq_uncut_inside (by omega : 1 ≤ n+1)
    μ Q hQ hnp (unpackDisorder g) u e k α x hr hs]
  exact congrArg (fun f : Vector (n+1) → ℝ => gradient f x) hfun

end SlowEquilibration.ConditionedEntrance
