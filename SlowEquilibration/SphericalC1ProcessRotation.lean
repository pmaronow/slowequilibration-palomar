-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWienerAugmentedRotation

/-! Almost-sure orthogonal covariance of the genuine globally constructed
physical C¹ spherical Langevin process, on every fixed finite horizon. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalModel SphericalWienerRotation
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {N : ℕ}

theorem c1Process_rotated_ae
    (hN : N ≠ 0) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (β : ℝ) (g g' : State N → State N)
    (hg : ContDiff ℝ 1 g) (hg' : ContDiff ℝ 1 g')
    (hgrad : ∀ v, g' (U v) = U (g v))
    (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, t ≤ T →
      SphericalC1Dynamics.process β g' hg' (U x) t (rotateWiener U ω) =
        U (SphericalC1Dynamics.process β g hg x t ω) := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let φ := rotateWiener U
  let hφ : MeasurePreserving φ P P := rotateWiener_measurePreserving U
  let D : BrownianDriver N P F := NullAugmentation.driver (VectorBrownian.driver N)
  let E : BrownianDriver N P F := rotatedCanonicalDriver U hφ
  let X := SphericalC1Dynamics.process β g hg x
  let Y := fun s ω => SphericalC1Dynamics.process β g' hg' (U x) s (φ ω)
  let Z := fun s ω => U (X s ω)
  have hfiltered : ∀ t, @Measurable _ _ (F t) (F t) φ :=
    rotateWiener_augmented_filtered U hφ
  have hpull : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => D.coordinate j t (φ ω) := by
    intro j t
    exact .of_forall (fun ω => rotatedCanonicalDriver_coordinate U hφ j t ω)
  have hmix : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => ∑ i : Fin N, (U (basisVector i)) j * D.coordinate i t ω := by
    intro j t
    exact .of_forall (fun ω => rotatedCanonicalDriver_coordinate_mix U hφ j t ω)
  have hXsol : IsLocalStrongSolutionOn
      (fun a v => (drift β g v) a)
      (fun a i v => (noiseColumn v i) a)
      CutoffSphere.physical_noise_continuous D x X T :=
    SphericalC1Dynamics.process_physical hN β g hg x hx T
  have hYsol : IsLocalStrongSolutionOn
      (fun a v => (drift β g' v) a)
      (fun a i v => (noiseColumn v i) a)
      CutoffSphere.physical_noise_continuous E (U x) Y T :=
    localStrongSolution_pullback hφ hfiltered D E hpull
      (fun a v => (drift β g' v) a)
      (fun a i v => (noiseColumn v i) a)
      CutoffSphere.physical_noise_continuous (U x)
      (SphericalC1Dynamics.process β g' hg' (U x)) T
      (SphericalC1Dynamics.process_physical hN β g' hg' (U x)
        (onSphere_map U hx) T)
  have hXsphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω) :=
    SphericalC1Dynamics.process_onSphere hN β g hg x hx
  have hZsol : IsLocalStrongSolutionOn
      (fun a v => (drift β g' v) a)
      (fun a i v => (noiseColumn v i) a)
      CutoffSphere.physical_noise_continuous E (U x) Z T := by
    exact physicalSolution_rotated U D E hmix β g g' hg hgrad x X T hXsol
      (fun k j t _ => sphere_rotatedNoise_timeCut_memLp hN U X
        hXsol.choose hXsol.choose_spec.choose hXsphere k j t)
  have hZsphere : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (Z t ω) :=
    hXsphere.mono (fun ω hω t _ => onSphere_map U (hω t))
  have hYsphere : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (Y t ω) :=
    (hφ.quasiMeasurePreserving.ae
      (SphericalC1Dynamics.process_onSphere hN β g' hg' (U x)
        (onSphere_map U hx))).mono (fun _ hω t _ => hω t)
  exact (SphericalC1Dynamics.physicalSolution_unique E β g' hg'
    (U x) T Z Y hZsol hYsol hZsphere hYsphere).mono
      (fun _ hω t ht => (hω t ht).symm)

end SlowEquilibration.SphericalRotationCovariance
