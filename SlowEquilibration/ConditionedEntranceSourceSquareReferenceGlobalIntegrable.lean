-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisFibreIntegrableTilt
public import SlowEquilibration.ConditionedEntranceJointSignedReducedEnergy

/-! The physical weighted square and killed reference densities are L¹
under the genuine global source tilt. Their uniform fibre bounds come
from the regular reference and the unit killed resolvent. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem source_joint_square_reference_globalTilt_integrable
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (J : Disorder N μ.maxDegree) (e k : ℝ)
    (F U : SourceParameters N μ × Vector N → ℝ)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (hphys : ∀ v : Vector N, OnSphere v →
      ∀ᵐ x ∂gibbsLaw N β
        (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ),
        ‖F ((J,(v,(e,k))),x)‖ ≤
          1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
        0 ≤ U ((J,(v,(e,k))),x) ∧ U ((J,(v,(e,k))),x) ≤ 1)
    (M : ℝ) (hM : 0 < M) :
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun v x =>
      sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β*(H z.1 z.2-H₀ z.2)
    Integrable (fun z : Vector N×Vector N =>
      F ((J,(z.1,(e,k))),z.2)*U ((J,(z.1,(e,k))),z.2)^2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) ∧
    Integrable (fun z : Vector N×Vector N =>
      PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,k))),z.2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) := by
  dsimp only
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun v x =>
    sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
  let fA : Vector N×Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,k))),z.2)*U ((J,(z.1,(e,k))),z.2)^2
  let fR : Vector N×Vector N → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,k))),z.2)
  let C := 1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))
  have hC : 0 ≤ C := by positivity
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector N × Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) by fun_prop)
  have hpair : Measurable (fun z : Vector N × Vector N =>
      (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) := by fun_prop
  have hFm : StronglyMeasurable (fun z : Vector N × Vector N =>
      F ((J,(z.1,(e,k))),z.2)) := hF.comp_measurable hpair
  have hUm : StronglyMeasurable (fun z : Vector N × Vector N =>
      U ((J,(z.1,(e,k))),z.2)) := hU.comp_measurable hpair
  have hAm : StronglyMeasurable fA := hFm.mul (hUm.pow 2)
  have hκm : StronglyMeasurable (fun z : Vector N×Vector N =>
      PhysicalHitting.capKilling α z.1 z.2) :=
    (capKilling_jointContinuous α).stronglyMeasurable
  have hRm : StronglyMeasurable fR := hκm.mul hFm
  have hAi : Integrable fA (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2)) M) := by
    apply axis_gibbs_uniform_fibre_integrable_globalTilt hN β H₀ hH₀ H hH
      fA hAm C hC ?_ M hM
    intro v hv
    let π := gibbsLaw N β (H v)
    have hHv : Continuous (H v) :=
      (sourceSmoothCutoffField_contDiff hN μ Q hQ hnp J v e k α χ hχ).continuous
    let : IsProbabilityMeasure π := gibbsLaw_probability hN β hHv
    have hfm : Measurable (fun x => fA (v,x)) :=
      (hAm.comp_measurable (measurable_const.prodMk measurable_id)).measurable
    have hbound : ∀ᵐ x ∂π, ‖fA (v,x)‖ ≤ C := by
      filter_upwards [hphys v hv] with x hx
      have hU2 : U ((J,(v,(e,k))),x)^2 ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.2)
          (show 0 ≤ 1+U ((J,(v,(e,k))),x) by linarith)]
      change ‖F ((J,(v,(e,k))),x)*U ((J,(v,(e,k))),x)^2‖ ≤ C
      rw [norm_mul]
      have hUnorm : ‖U ((J,(v,(e,k))),x)^2‖ = U ((J,(v,(e,k))),x)^2 := by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      rw [hUnorm]
      exact (mul_le_mul_of_nonneg_left hU2 (norm_nonneg _)).trans
        (by simpa only [mul_one] using hx.1)
    have hi : Integrable (fun x => fA (v,x)) π :=
      Integrable.of_bound hfm.aestronglyMeasurable C hbound
    refine ⟨hi,?_⟩
    have hh := integral_mono_ae hi.abs (integrable_const C) hbound
    simpa only [integral_const,probReal_univ,one_smul,Real.norm_eq_abs] using hh
  have hRi : Integrable fR (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2)) M) := by
    apply axis_gibbs_uniform_fibre_integrable_globalTilt hN β H₀ hH₀ H hH
      fR hRm C hC ?_ M hM
    intro v hv
    let π := gibbsLaw N β (H v)
    have hHv : Continuous (H v) :=
      (sourceSmoothCutoffField_contDiff hN μ Q hQ hnp J v e k α χ hχ).continuous
    let : IsProbabilityMeasure π := gibbsLaw_probability hN β hHv
    have hfm : Measurable (fun x => fR (v,x)) :=
      (hRm.comp_measurable (measurable_const.prodMk measurable_id)).measurable
    have hbound : ∀ᵐ x ∂π, ‖fR (v,x)‖ ≤ C := by
      filter_upwards [hphys v hv] with x hx
      change ‖PhysicalHitting.capKilling α v x*F ((J,(v,(e,k))),x)‖ ≤ C
      rw [norm_mul,Real.norm_eq_abs,
        abs_of_nonneg (PhysicalHitting.capKilling_nonneg α v x)]
      exact (mul_le_mul (PhysicalHitting.capKilling_le_one hα v x) hx.1
        (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
    have hi : Integrable (fun x => fR (v,x)) π :=
      Integrable.of_bound hfm.aestronglyMeasurable C hbound
    refine ⟨hi,?_⟩
    have hh := integral_mono_ae hi.abs (integrable_const C) hbound
    simpa only [integral_const,probReal_univ,one_smul,Real.norm_eq_abs] using hh
  exact ⟨hAi,hRi⟩

end SlowEquilibration.ConditionedEntrance
