-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureCutoffInterior
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralSemigroup
public import SlowEquilibration.ConditionedEntranceSourceActualLocalCoupling

/-! Local pathwise coupling of the actual proper pure value posterior and
the physical two-coordinate pure source cutoff on the same Wiener path. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalDynamics
open SphericalPosteriorMaps SphericalC1Dynamics
open SphericalPosteriorGradientIndependence SphericalSmoothTensorStationarity
open SphericalAging HardSphereDynamics
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem actual_pureValuePosterior_sourceCutoff_agree_before_exit
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (hQ : 0 < Q)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e α : ℝ) (β : ℝ)
    (x : Vector (n+1)) (hx : OnSphere x) (T : ℝ≥0) :
    let μ := FiniteMixture.pure p hp c hc
    let J := unpackDisorder g
    let Jpost := unpackDisorder (valuePosterior n μ Q u e g)
    let G := surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
    let D := SmoothKilledGeneral.FieldData.ofPure (by omega : 1 ≤ n+1)
      p hp c hc Q J u e α sourceScalarCutoff sourceScalarCutoff_contDiff_two
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t, t ≤ T →
      (∀ s, s < t →
        max |overlap (mixedProcess μ Jpost β x s ω) u / α|
          |inner ℝ G (mixedProcess μ Jpost β x s ω) /
              (((n+1 : ℕ) : ℝ) * α)| < 1) →
      mixedProcess μ Jpost β x t ω =
        SmoothKilledGeneral.process D β x t ω := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let J := unpackDisorder g
  let Jpost := unpackDisorder (valuePosterior n μ Q u e g)
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  let D := SmoothKilledGeneral.FieldData.ofPure (by omega : 1 ≤ n+1)
    p hp c hc Q J u e α sourceScalarCutoff sourceScalarCutoff_contDiff_two
  let z : Vector (n+1) → ℝ := fun y =>
    max |overlap y u / α| |inner ℝ G y / (((n+1 : ℕ) : ℝ)*α)|
  have hz : Continuous z := by dsimp only [z,overlap]; fun_prop
  have hgrad : ∀ y, z y < 1 → mixedGradient μ Jpost y =
      smoothGradient D.hamiltonian D.hamiltonian_contDiff y := by
    intro y hy
    have hr : |overlap y u / α| < 1 := (max_lt_iff.mp hy).1
    have hs : |inner ℝ G y / (((n+1 : ℕ) : ℝ)*α)| < 1 :=
      (max_lt_iff.mp hy).2
    have hh := pureSourceSmoothCutoffField_gradient_eq_actual_valuePosterior_inside
      n p hp c hc hQ g u ((onSphere_iff_norm_sq u).mp hu) e α y hr hs
    change gradient (fieldOfMixture μ Jpost) y = gradient D.hamiltonian y
    rw [show D.hamiltonian =
      pureSourceSmoothCutoffField p hp c hc Q J u e α sourceScalarCutoff from
      SmoothKilledGeneral.FieldData.ofPure_hamiltonian
        (by omega : 1 ≤ n+1) p hp c hc Q J u e α sourceScalarCutoff
          sourceScalarCutoff_contDiff_two]
    exact hh.symm
  have hlocal := SphericalC1LocalAgreement.c1Process_agree_before_open_exit_anyInitial
    (by omega : n+1 ≠ 0) β (mixedGradient μ Jpost)
      (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      ((mixedGradient_contDiff μ Jpost).of_le (by simp))
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff)
      z hz hgrad x hx T
  filter_upwards [hlocal,
    mixedProcess_ae_C1Process (by omega : 1 ≤ n+1) μ Jpost β x hx,
    SmoothKilledGeneral.process_ae_actual D β x] with ω hloc hmix hcut
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
    _ = SmoothKilledGeneral.process D β x t ω := (hcut t).symm

end SlowEquilibration.ConditionedEntrance
