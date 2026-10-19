module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalTransitionRotation

@[expose] public section

/-! # The physical diffusion depends only on the actual spherical field

Raw mixed tensors have redundant coefficients. Equality of their fields
on the sphere implies equality of actual Gibbs laws and physical kernels,
even when the ambient polynomial extensions differ. The kernel equality
is derived from the actual backward PDE and Gibbs integration by parts.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace NNReal
variable {N : ℕ}

theorem gibbsLaw_congr_onSphere (hN : 1 ≤ N) (β : ℝ)
    {H K : Vector N → ℝ} (hH : ∀ x, OnSphere x → H x=K x) :
    gibbsLaw N β H=gibbsLaw N β K := by
  have hp : partition N β H=partition N β K := by
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    rw [hH x ((onSphere_iff_norm_sq x).mpr hx)]
  apply withDensity_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  simp only [gibbsDensity,hp,hH x ((onSphere_iff_norm_sq x).mpr hx)]

lemma mixedGenerator_pairing_field_congr (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree) (β : ℝ)
    (hfield : ∀ x, OnSphere x → fieldOfMixture μ J x=fieldOfMixture μ K x)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x, mixedGenerator μ J β f x*g x ∂mixtureGibbsLaw μ β J)=
      ∫ x, f x*mixedGenerator μ K β g x ∂mixtureGibbsLaw μ β J := by
  have hπ := gibbsLaw_congr_onSphere hN β hfield
  have hleft := mixedGenerator_integration_by_parts hN μ J β (hg.of_le (by norm_num)) hf
  have hright := mixedGenerator_integration_by_parts hN μ K β (hf.of_le (by norm_num)) hg
  have hform : dirichletForm N β (fieldOfMixture μ J) f g=
      dirichletForm N β (fieldOfMixture μ K) f g := by
    unfold dirichletForm
    rw [hπ]
  have hπ' : mixtureGibbsLaw μ β J=mixtureGibbsLaw μ β K := hπ
  calc
    _ = ∫ x, g x*mixedGenerator μ J β f x ∂mixtureGibbsLaw μ β J := by
      apply integral_congr_ae
      exact .of_forall fun x => mul_comm _ _
    _ = -dirichletForm N β (fieldOfMixture μ J) g f := hleft
    _ = -dirichletForm N β (fieldOfMixture μ J) f g := by rw [dirichletForm_symmetric]
    _ = -dirichletForm N β (fieldOfMixture μ K) f g := congrArg Neg.neg hform
    _ = ∫ x, f x*mixedGenerator μ K β g x ∂mixtureGibbsLaw μ β K := hright.symm
    _ = _ := by rw [hπ']

def fieldInterpolation (μ : FiniteMixture) (J K : Disorder N μ.maxDegree) (β : ℝ)
    (f g : Vector N → ℝ) (t z : ℝ) : ℝ :=
  ∫ x, realExpectation μ J β f (t-z) x*realExpectation μ K β g z x ∂mixtureGibbsLaw μ β J

lemma fieldInterpolation_continuous (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree) (β : ℝ)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ) :
    Continuous (fieldInterpolation μ J K β f g t) := by
  let := mixtureGibbsLaw_probability hN μ β J
  apply CompactMeasure.continuous_integral (mixtureGibbsLaw μ β J)
    {x : Vector N | OnSphere x} (physicalSphere_compact N) (mixtureGibbsLaw_onSphere hN μ J β)
  exact ((realExpectation_joint_continuous μ J β hf hfc).comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)).mul
      (realExpectation_joint_continuous μ K β hg hgc)

lemma fieldInterpolation_hasDerivAt_zero (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree) (β : ℝ)
    (hfield : ∀ x, OnSphere x → fieldOfMixture μ J x=fieldOfMixture μ K x)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t z : ℝ) (hz : 0 < z) (hzt : z < t) :
    HasDerivAt (fieldInterpolation μ J K β f g t) 0 z := by
  let := mixtureGibbsLaw_probability hN μ β J
  let Fv := realExpectation μ J β f
  let Gv := realExpectation μ K β g
  let Iv : ℝ → Vector N → ℝ := fun r x => Fv (t-r) x*Gv r x
  let Id : ℝ → Vector N → ℝ := fun r x =>
    -(mixedGenerator μ J β (Fv (t-r)) x)*Gv r x+
      Fv (t-r) x*mixedGenerator μ K β (Gv r) x
  have hF : Continuous (Function.uncurry Fv) := realExpectation_joint_continuous μ J β hf hfc
  have hG : Continuous (Function.uncurry Gv) := realExpectation_joint_continuous μ K β hg hgc
  have hLF : Continuous (fun q : ℝ × Vector N => mixedGenerator μ J β (Fv q.1) q.2) :=
    realExpectation_generator_joint_continuous μ J β hf hfc
  have hLG : Continuous (fun q : ℝ × Vector N => mixedGenerator μ K β (Gv q.1) q.2) :=
    realExpectation_generator_joint_continuous μ K β hg hgc
  have hback : Continuous (fun q : ℝ × Vector N => (t-q.1,q.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hIv : Continuous (Function.uncurry Iv) := (hF.comp hback).mul hG
  have hId : Continuous (Function.uncurry Id) :=
    ((hLF.comp hback).neg.mul hG).add ((hF.comp hback).mul hLG)
  have hd := CompactMeasure.hasDerivAt_integral (mixtureGibbsLaw μ β J)
    {x : Vector N | OnSphere x} (physicalSphere_compact N)
    (mixtureGibbsLaw_onSphere hN μ J β) hIv hId 0 t z hz hzt (by
      intro r hr x hx
      have hdF := (mixedExpectation_backward (by omega) μ J β x hx hf hfc (t-r)
        (sub_pos.mpr hr.2)).comp r ((hasDerivAt_id r).const_sub t)
      have hdG := mixedExpectation_backward (by omega) μ K β x hx hg hgc r hr.1
      have hdf : HasDerivAt (fun s => Fv (t-s) x) (-mixedGenerator μ J β (Fv (t-r)) x) r := by
        dsimp only [Fv,realExpectation]
        convert hdF using 1 <;> (try simp only [Function.comp_def,mul_neg_one])
        rfl
      exact hdf.mul hdG)
  have hFz : ContDiff ℝ 2 (Fv (t-z)) := realExpectation_contDiff μ J β hf hfc _
  have hGz : ContDiff ℝ 2 (Gv z) := realExpectation_contDiff μ K β hg hgc _
  have hcross := mixedGenerator_pairing_field_congr hN μ J K β hfield hFz hGz
  have hi1 : Integrable (fun x => mixedGenerator μ J β (Fv (t-z)) x*Gv z x)
      (mixtureGibbsLaw μ β J) := integrable_gibbs_of_continuous hN β
    (fieldOfMixture_contDiff μ J).continuous
    ((Ito.generator_continuous β _ (mixedGradient_contDiff μ J) hFz).mul hGz.continuous)
  have hi2 : Integrable (fun x => Fv (t-z) x*mixedGenerator μ K β (Gv z) x)
      (mixtureGibbsLaw μ β J) := integrable_gibbs_of_continuous hN β
    (fieldOfMixture_contDiff μ J).continuous
    (hFz.continuous.mul (Ito.generator_continuous β _ (mixedGradient_contDiff μ K) hGz))
  have hzero : (∫ x, Id z x ∂mixtureGibbsLaw μ β J)=0 := by
    dsimp [Id]
    simp_rw [neg_mul]
    rw [integral_add (f := fun x => -(mixedGenerator μ J β (Fv (t-z)) x*Gv z x))
      (g := fun x => Fv (t-z) x*mixedGenerator μ K β (Gv z) x) hi1.neg hi2,integral_neg,hcross]
    ring
  rw [hzero] at hd
  exact hd

lemma compact_field_pairing (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree) (β : ℝ)
    (hfield : ∀ x, OnSphere x → fieldOfMixture μ J x=fieldOfMixture μ K x)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ≥0) :
    (∫ x, f x*mixedExpectation μ J β t g x ∂mixtureGibbsLaw μ β J)=
      ∫ x, f x*mixedExpectation μ K β t g x ∂mixtureGibbsLaw μ β J := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
    (fieldInterpolation_continuous hN μ J K β hf hfc hg hgc t).continuousOn
    (fun z hz => fieldInterpolation_hasDerivAt_zero hN μ J K β hfield hf hfc hg hgc t z hz.1 hz.2)
    ((continuous_const : Continuous (fun _ : ℝ => (0:ℝ))).intervalIntegrable 0 t)
  simp only [intervalIntegral.integral_zero,fieldInterpolation,sub_self,sub_zero,realExpectation_zero] at hh
  have he : (∫ x, mixedExpectation μ J β t f x*g x ∂mixtureGibbsLaw μ β J)=
      ∫ x, f x*mixedExpectation μ K β t g x ∂mixtureGibbsLaw μ β J := by
    simpa only [realExpectation,Real.toNNReal_coe] using (sub_eq_zero.mp hh.symm).symm
  exact (compact_mixedExpectation_reversible hN μ J β hf hfc hg hgc t).symm.trans he

theorem compact_mixedExpectation_field_congr (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree) (β : ℝ)
    (hfield : ∀ x, OnSphere x → fieldOfMixture μ J x=fieldOfMixture μ K x)
    {g : Vector N → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    mixedExpectation μ J β t g x=mixedExpectation μ K β t g x := by
  let D : Vector N → ℝ := fun y => mixedExpectation μ J β t g y-mixedExpectation μ K β t g y
  have hD : ContDiff ℝ 2 D := ((mixedExpectation_regular μ J β hg hgc).1 t).sub
    ((mixedExpectation_regular μ K β hg hgc).1 t)
  obtain ⟨f,hf,hfc,hagree⟩ := exists_C2_cutoff D hD
  have hpair := compact_field_pairing hN μ J K β hfield hf hfc hg hgc t
  have hi1 : Integrable (fun y => f y*mixedExpectation μ J β t g y) (mixtureGibbsLaw μ β J) :=
    integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous
      (hf.continuous.mul ((mixedExpectation_regular μ J β hg hgc).1 t).continuous)
  have hi2 : Integrable (fun y => f y*mixedExpectation μ K β t g y) (mixtureGibbsLaw μ β J) :=
    integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous
      (hf.continuous.mul ((mixedExpectation_regular μ K β hg hgc).1 t).continuous)
  have hz : (∫ y, (D y)^2 ∂mixtureGibbsLaw μ β J)=0 := by
    calc
      _ = ∫ y, f y*mixedExpectation μ J β t g y-f y*mixedExpectation μ K β t g y
          ∂mixtureGibbsLaw μ β J := by
        apply integral_congr_ae
        filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with y hy
        rw [(hagree y hy).1]
        dsimp [D]
        ring
      _ = _ := by rw [integral_sub hi1 hi2,hpair]; ring
  have hiD : Integrable (fun y => (D y)^2) (mixtureGibbsLaw μ β J) :=
    integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous (hD.continuous.pow 2)
  have haeSq := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (D y)) hiD).mp hz
  have hae : D =ᵐ[mixtureGibbsLaw μ β J] 0 := haeSq.mono (fun y hy => sq_eq_zero_iff.mp hy)
  have he := continuous_eq_zero_onSphere_of_gibbs_ae hN β (fieldOfMixture_contDiff μ J).continuous
    hD.continuous hae x hx
  exact sub_eq_zero.mp he

/-- The actual transition law depends only on the field restricted to the
sphere. Ambient radial terms and redundant tensor coefficients disappear
from the true physical kernel, as required for source field independence. -/
theorem mixedTransitionKernel_congr_onSphere (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree) (β : ℝ)
    (hfield : ∀ y, OnSphere y → fieldOfMixture μ J y=fieldOfMixture μ K y)
    (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    mixedTransitionKernel μ J β t x=mixedTransitionKernel μ K β t x := by
  have hsupport : ∀ᵐ y ∂mixedTransitionKernel μ J β t x, OnSphere y := by
    rw [mixedTransitionKernel_apply,mixedTransitionLaw]
    exact (ae_map_iff (mixedProcess_measurable μ J β x t).aemeasurable (sphere_measurableSet N)).2
      ((mixedProcess_onSphere (by omega) μ J β x hx).mono fun _ h => h t)
  have hsupportK : ∀ᵐ y ∂mixedTransitionKernel μ K β t x, OnSphere y := by
    rw [mixedTransitionKernel_apply,mixedTransitionLaw]
    exact (ae_map_iff (mixedProcess_measurable μ K β x t).aemeasurable (sphere_measurableSet N)).2
      ((mixedProcess_onSphere (by omega) μ K β x hx).mono fun _ h => h t)
  apply SphericalAging.SphereSmoothTestMeasureExt.measure_eq_of_compactC2_integrals hsupport hsupportK
  intro g hg hgc
  rw [← mixedExpectation_eq_kernel μ J β t g hg.continuous.stronglyMeasurable x,
    ← mixedExpectation_eq_kernel μ K β t g hg.continuous.stronglyMeasurable x]
  exact compact_mixedExpectation_field_congr hN μ J K β hfield hg hgc t x hx

end
end SlowEquilibration.SphericalRotationCovariance
