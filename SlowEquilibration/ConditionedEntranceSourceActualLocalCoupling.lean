-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1LocalAgreementAny
public import SlowEquilibration.ConditionedEntranceSourceCutoffInterior
public import SlowEquilibration.SphericalPosteriorGradientShortCells
public import SlowEquilibration.ConditionedEntranceSourceJointKilling
public import SlowEquilibration.ConditionedEntranceSmoothKilledSemigroup

/-! Local pathwise coupling of the actual Gaussian-regression posterior and
the physical source cutoff diffusion, on the same canonical Wiener path. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalDynamics
open SphericalPosteriorMaps SphericalMarkedWindows
open SphericalPosteriorGradientIndependence SphericalC1Dynamics
open SphericalSmoothTensorStationarity
open SphericalAging HardSphereDynamics SmoothKilled
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem actual_mixedPosterior_sourceCutoff_agree_before_exit
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree)
    (g : EuclideanDisorder (n+1) μ.maxDegree)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e k α : ℝ) (hα : 0 < α) (β : ℝ)
    (x : Vector (n+1)) (hx : OnSphere x) (T : ℝ≥0) :
    let J := unpackDisorder g
    let Jpost := unpackDisorder
      (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)
    let G := surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
    let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
      μ hnp Q hQ hQ1 α hα sourceScalarCutoff sourceScalarCutoff_contDiff_two
      (J,(u,(e,k))) hu
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t, t ≤ T →
      (∀ s, s < t →
        max |overlap (mixedProcess μ Jpost β x s ω) u / α|
          |inner ℝ G (mixedProcess μ Jpost β x s ω) /
              (((n+1 : ℕ) : ℝ) * α)| < 1) →
      mixedProcess μ Jpost β x t ω = SmoothKilled.process D β x t ω := by
  dsimp only
  let J := unpackDisorder g
  let Jpost := unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
    μ hnp Q hQ hQ1 α hα sourceScalarCutoff sourceScalarCutoff_contDiff_two
    (J,(u,(e,k))) hu
  let z : Vector (n+1) → ℝ := fun y =>
    max |overlap y u / α| |inner ℝ G y / (((n+1 : ℕ) : ℝ)*α)|
  have hz : Continuous z := by
    dsimp only [z,overlap]
    fun_prop
  have hgrad : ∀ y, z y < 1 → mixedGradient μ Jpost y =
      smoothGradient D.hamiltonian D.hamiltonian_contDiff y := by
    intro y hy
    have hr : |overlap y u / α| < 1 := (max_lt_iff.mp hy).1
    have hs : |inner ℝ G y / (((n+1 : ℕ) : ℝ)*α)| < 1 :=
      (max_lt_iff.mp hy).2
    have hh := sourceSmoothCutoffField_gradient_eq_actual_mixedPosterior_inside
      n μ Q hQ hnp g u ((onSphere_iff_norm_sq u).mp hu) e k α y hr hs
    exact hh.symm
  have hlocal := SphericalC1LocalAgreement.c1Process_agree_before_open_exit_anyInitial
    (by omega : n+1 ≠ 0) β (mixedGradient μ Jpost)
      (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      ((mixedGradient_contDiff μ Jpost).of_le (by simp))
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff)
      z hz hgrad x hx T
  filter_upwards [hlocal,
    mixedProcess_ae_C1Process (by omega : 1 ≤ n+1) μ Jpost β x hx,
    SmoothKilled.process_ae_actual D β x] with ω hloc hmix hcut
  intro t ht hbefore
  calc
    mixedProcess μ Jpost β x t ω =
        SphericalC1Dynamics.process β (mixedGradient μ Jpost)
          ((mixedGradient_contDiff μ Jpost).of_le (by simp)) x t ω := hmix t
    _ = SphericalC1Dynamics.process β
          (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
          (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x t ω := by
      apply hloc t ht
      intro s hs
      simpa only [z, ← hmix s] using hbefore s hs
    _ = SmoothKilled.process D β x t ω := (hcut t).symm

end SlowEquilibration.ConditionedEntrance
