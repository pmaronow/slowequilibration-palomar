-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.CompactSupportedCoefficientFamily
public import SlowEquilibration.SphericalEnergy
public import SphericalAging.HardSphereStochastic
public import SphericalAging.LandscapeDerivatives

/-! A fixed smooth spatial localization turns actual jointly continuous
spherical coefficients into a continuous bounded-coefficient family while
preserving their exact values on the physical sphere. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped BoundedContinuousFunction InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ]

def sphericalLocalizationBump (N : ℕ) : ContDiffBump (0 : Vector N) :=
  coefficientBump (Real.sqrt (N : ℝ)+1) (by positivity)

theorem sphericalLocalizationBump_one (x : Vector N) (hx : OnSphere x) :
    sphericalLocalizationBump N x=1 := by
  apply (sphericalLocalizationBump N).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  have hn := SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  change ‖x‖ ≤ Real.sqrt (N : ℝ)+1
  linarith

omit [TopologicalSpace Θ] in
theorem localized_support (F : Θ × Vector N → ℝ) (p : Θ) :
    Function.support (fun x => sphericalLocalizationBump N x*F (p,x)) ⊆
      Metric.closedBall (0 : Vector N) (sphericalLocalizationBump N).rOut := by
  intro x hx
  have hb : x∈Function.support (sphericalLocalizationBump N) := by
    intro hz
    exact hx (by change sphericalLocalizationBump N x*F (p,x)=0;rw [hz,zero_mul])
  rw [(sphericalLocalizationBump N).support_eq] at hb
  exact Metric.ball_subset_closedBall hb

def sphericalLocalizedFamily (F : Θ × Vector N → ℝ) (hF : Continuous F) : Θ → Vector N →ᵇ ℝ :=
  CompactSupportedCoefficientFamily.boundedFamily
    (Metric.closedBall (0 : Vector N) (sphericalLocalizationBump N).rOut) (isCompact_closedBall _ _)
    (fun z => sphericalLocalizationBump N z.2*F z)
    (((sphericalLocalizationBump N).continuous.comp continuous_snd).mul hF) (localized_support F)

theorem sphericalLocalizedFamily_continuous (F : Θ × Vector N → ℝ) (hF : Continuous F) :
    Continuous (sphericalLocalizedFamily F hF) :=
  CompactSupportedCoefficientFamily.boundedFamily_continuous _ _ _ _ _

theorem sphericalLocalizedFamily_apply (F : Θ × Vector N → ℝ) (hF : Continuous F)
    (p : Θ) (x : Vector N) : sphericalLocalizedFamily F hF p x=sphericalLocalizationBump N x*F (p,x) := rfl

theorem sphericalLocalizedFamily_ae (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (F : Θ × Vector N → ℝ) (hF : Continuous F) (p : Θ) :
    sphericalLocalizedFamily F hF p=ᵐ[gibbsLaw N β H] fun x => F (p,x) := by
  filter_upwards [gibbsLaw_support hN β H] with x hx
  rw [sphericalLocalizedFamily_apply,sphericalLocalizationBump_one x ((onSphere_iff_norm_sq x).mpr hx),one_mul]

/-- Strict positivity of the actual coefficient on the compact state set
produces the required genuine local coercivity constant. -/
theorem sphericalLocalizedFamily_positive_lower (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (F : Θ × Vector N → ℝ) (hF : Continuous F) (p : Θ)
    (hFp : ∀ x,0 < F (p,x)) :
    ∃ c : ℝ,0<c ∧ ∀ᵐ x ∂gibbsLaw N β H,c ≤ sphericalLocalizedFamily F hF p x := by
  have hFc : Continuous (fun x => F (p,x)) := hF.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x₀,hx₀,hmin⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).exists_isMinOn
    (Metric.nonempty_closedBall.mpr (Real.sqrt_nonneg _)) hFc.continuousOn
  refine ⟨F (p,x₀),hFp x₀,?_⟩
  have hball := (sphereLaw_mem_closedBall hN).filter_mono (gibbsLaw_absolutelyContinuous β H).ae_le
  filter_upwards [hball,sphericalLocalizedFamily_ae hN β H F hF p] with x hx he
  rw [he]
  exact hmin hx

end SlowEquilibration.SphericalForm
