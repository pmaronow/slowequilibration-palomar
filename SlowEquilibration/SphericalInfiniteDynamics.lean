-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1Dynkin
public import SlowEquilibration.SphericalInfiniteGibbs

/-! The actual infinite tensor field drives a genuine spherical strong
solution. Its drift is identified with the intrinsic gradient of the literal
series on the proved probability-one regularity event. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set MeasureTheory ProbabilityTheory Filter SphericalModel
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalDynamics SphericalIntrinsicExtension SphericalForm
open scoped NNReal ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Gradient of the actual globally C² representative of the literal field. -/
def infiniteGradient (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) :
    Vector (n+1) → Vector (n+1) := gradient (regularAmbientField n μ J)

theorem infiniteGradient_contDiff (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) :
    ContDiff ℝ 1 (infiniteGradient n μ J) := by
  unfold infiniteGradient gradient
  exact ((InnerProductSpace.toDual ℝ (Vector (n+1))).symm.contDiff).comp
    ((regularAmbientField_contDiff n μ J).fderiv_right (by norm_num))

/-- Exact manuscript physical drift, with the curvature correction. -/
def infiniteDrift (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) (β : ℝ) :
    Vector (n+1) → Vector (n+1) := drift β (infiniteGradient n μ J)

/-- The drift on the sphere is the genuine intrinsic gradient of the
literal random series; the regular ambient representative introduces no
change in the spherical dynamics. -/
theorem infiniteDrift_eq_intrinsic (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (x : RoundSphere n) :
    infiniteDrift n μ J β x = β • intrinsicGradient n (intrinsicField n μ J) x -
      (1-1/((n+1:ℕ):ℝ)) • (x : Vector (n+1)) := by
  have hk : kappa (n+1)=1-1/(n+1:ℕ) := by unfold kappa; field_simp
  rw [infiniteDrift,drift,hk]
  congr 1
  change β • projection (x : Vector (n+1)) (gradient (regularAmbientField n μ J) x)=_
  rw [regularAmbientField,ite_eq_left hJ,intrinsicGradient,surfaceGradient,tangentProjection_apply]

/-- Actual canonical Brownian-path solution for the infinite-field drift. -/
def infiniteProcess (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) (β : ℝ)
    (x : Vector (n+1)) : ℝ≥0 → VectorBrownian.Space (n+1) → Vector (n+1) :=
  SphericalC1Dynamics.process β (infiniteGradient n μ J) (infiniteGradient_contDiff n μ J) x

theorem infiniteProcess_onSphere (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (hx : OnSphere x) :
    ∀ᵐ omega ∂VectorBrownian.law (n+1),∀ t,OnSphere (infiniteProcess n μ J β x t omega) :=
  SphericalC1Dynamics.process_onSphere (by omega) β _ (infiniteGradient_contDiff n μ J) x hx

theorem infiniteProcess_physical (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (hx : OnSphere x) (T : ℝ≥0) :
    IsLocalStrongSolutionOn (fun i z => infiniteDrift n μ J β z i)
      (fun i j z => noiseColumn z j i) CutoffSphere.physical_noise_continuous
      (NullAugmentation.driver (VectorBrownian.driver (n+1))) x (infiniteProcess n μ J β x) T :=
  SphericalC1Dynamics.process_physical (by omega) β _ (infiniteGradient_contDiff n μ J) x hx T

/-- Uniqueness of the actual infinite-field spherical diffusion among
sphere-valued strong solutions driven by the same Brownian motion. -/
theorem infiniteProcess_unique (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (hx : OnSphere x) (T : ℝ≥0)
    (Y : ℝ≥0 → VectorBrownian.Space (n+1) → Vector (n+1))
    (hY : IsLocalStrongSolutionOn (fun i z => infiniteDrift n μ J β z i)
      (fun i j z => noiseColumn z j i) CutoffSphere.physical_noise_continuous
      (NullAugmentation.driver (VectorBrownian.driver (n+1))) x Y T)
    (hYs : ∀ᵐ omega ∂VectorBrownian.law (n+1),∀ t,t≤T → OnSphere (Y t omega)) :
    ∀ᵐ omega ∂VectorBrownian.law (n+1),∀ t,t≤T → infiniteProcess n μ J β x t omega=Y t omega :=
  SphericalC1Dynamics.physicalSolution_unique _ β _ (infiniteGradient_contDiff n μ J)
    x T (infiniteProcess n μ J β x) Y (infiniteProcess_physical n μ J β x hx T) hY
    ((infiniteProcess_onSphere n μ J β x hx).mono (fun _ h t _ => h t)) hYs

theorem infiniteProcess_continuous (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) :
    ∀ᵐ omega ∂VectorBrownian.law (n+1),Continuous (fun t => infiniteProcess n μ J β x t omega) :=
  SphericalC1Dynamics.process_continuous β _ (infiniteGradient_contDiff n μ J) x

theorem infiniteProcess_measurable (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (t : ℝ≥0) : Measurable (infiniteProcess n μ J β x t) :=
  SphericalC1Dynamics.process_measurable β _ (infiniteGradient_contDiff n μ J) x t

/-- The measurable Markov kernel constructed from the actual infinite-field
Picard family, rather than a prescribed transition distribution. -/
def infiniteTransitionKernel (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (t : ℝ≥0) : Kernel (Vector (n+1)) (Vector (n+1)) :=
  SphericalC1Dynamics.transitionKernel β _ (infiniteGradient_contDiff n μ J) t

instance infiniteTransitionKernel_markov (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (t : ℝ≥0) : IsMarkovKernel (infiniteTransitionKernel n μ J β t) :=
  SphericalC1Dynamics.transitionKernel_markov β _ (infiniteGradient_contDiff n μ J) t

theorem infiniteTransitionKernel_law (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (t : ℝ≥0) (x : Vector (n+1)) :
    infiniteTransitionKernel n μ J β t x =
      (VectorBrownian.law (n+1)).map (infiniteProcess n μ J β x t) :=
  SphericalC1Dynamics.transitionKernel_apply β _ (infiniteGradient_contDiff n μ J) t x

theorem infiniteTransitionKernel_zero (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) : infiniteTransitionKernel n μ J β 0 x=Measure.dirac x :=
  SphericalC1Dynamics.transitionKernel_zero β _ (infiniteGradient_contDiff n μ J) x

theorem infiniteTransitionKernel_support (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (hx : OnSphere x) (t : ℝ≥0) :
    infiniteTransitionKernel n μ J β t x {y | OnSphere y}=1 :=
  SphericalC1Dynamics.transitionKernel_support (by omega) β _ (infiniteGradient_contDiff n μ J) x hx t

theorem infiniteTransitionKernel_semigroup (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (s t : ℝ≥0) (x : Vector (n+1)) :
    infiniteTransitionKernel n μ J β (s+t) x =
      (infiniteTransitionKernel n μ J β t ∘ₖ infiniteTransitionKernel n μ J β s) x :=
  SphericalC1Dynamics.transitionKernel_semigroup β _ (infiniteGradient_contDiff n μ J) s t x

/-- The literal second-order differential generator of the actual solution. -/
def infiniteDifferentialGenerator (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (f : Vector (n+1) → ℝ) : Vector (n+1) → ℝ :=
  sphericalCoefficientGenerator (n+1) β (regularAmbientField n μ J) f

theorem infiniteDifferentialGenerator_eq_rotation (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (β : ℝ) {f : Vector (n+1) → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vector (n+1)) (hx : OnSphere x) :
    infiniteDifferentialGenerator n μ J β f x=rotationGenerator (n+1) β (regularAmbientField n μ J) f x :=
  (rotationGenerator_eq_coefficientGenerator (by omega) β _ hf x hx).symm

/-- Actual C² Dynkin formula for the original infinite-field dynamics. -/
theorem infiniteProcess_dynkin (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (hx : OnSphere x) {f : Vector (n+1) → ℝ}
    (hf : ContDiff ℝ 2 f) (T : ℝ≥0) :
    (∫ omega,f (infiniteProcess n μ J β x T omega) ∂VectorBrownian.law (n+1)) = f x +
      ∫ s in (0:ℝ)..(T:ℝ),∫ omega,infiniteDifferentialGenerator n μ J β f
        (infiniteProcess n μ J β x s.toNNReal omega) ∂VectorBrownian.law (n+1) :=
  SphericalC1Dynamics.expectation_dynkin (by omega) β _ (infiniteGradient_contDiff n μ J) x hx hf T

theorem infiniteProcess_generator_at_zero (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (x : Vector (n+1)) (hx : OnSphere x) {f : Vector (n+1) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => ∫ omega,f (infiniteProcess n μ J β x s.toNNReal omega)
      ∂VectorBrownian.law (n+1)) (infiniteDifferentialGenerator n μ J β f x) (Ici 0) 0 :=
  SphericalC1Dynamics.expectation_hasDerivWithinAt_zero (by omega) β _
    (infiniteGradient_contDiff n μ J) x hx hf

/-- The genuine regularity event simultaneously identifies the driving
potential, intrinsic drift, and original Gibbs probability. -/
theorem infiniteDynamics_literal_ae (n : ℕ) (μ : InfiniteMixture) (β : ℝ) :
    ∀ᵐ J ∂disorderLaw (n+1),
      IntrinsicContDiff n 2 (intrinsicField n μ J) ∧
      IsProbabilityMeasure (gibbsLaw (n+1) β (field μ J)) ∧
      gibbsLaw (n+1) β (field μ J)=gibbsLaw (n+1) β (regularAmbientField n μ J) ∧
      ∀ x : RoundSphere n,infiniteDrift n μ J β x=
        β • intrinsicGradient n (intrinsicField n μ J) x-(1-1/((n+1:ℕ):ℝ)) • (x : Vector (n+1)) := by
  filter_upwards [summableJetDisorder_ae (by omega : 0<n+1) μ] with J hJ
  exact ⟨intrinsicField_contDiff n μ J hJ,literal_gibbsLaw_probability n μ β J hJ,
    literal_gibbsLaw_eq_regular n μ β J hJ,infiniteDrift_eq_intrinsic n μ J hJ β⟩

end SlowEquilibration.SphericalInfiniteModel
