module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalRotationCovariance

@[expose] public section

/-! # Rotation covariance of the actual mixed Langevin transitions

Cross-field interpolation uses the already constructed physical SDE backward
equations and the genuine transported Gibbs form. It supplies covariance of
the literal transition kernels, without a rotation-covariance premise.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace NNReal
variable {N : ℕ}

def rotationInterpolation (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (f g : Vector N → ℝ) (t z : ℝ) : ℝ :=
  ∫ x, realExpectation μ J β f (t-z) x *
    realExpectation μ (rotatedDisorder U J) β g z (U x) ∂mixtureGibbsLaw μ β J

lemma rotationInterpolation_continuous (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ) :
    Continuous (rotationInterpolation μ J β U f g t) := by
  let := mixtureGibbsLaw_probability hN μ β J
  apply CompactMeasure.continuous_integral (mixtureGibbsLaw μ β J)
    {x : Vector N | OnSphere x} (physicalSphere_compact N)
    (mixtureGibbsLaw_onSphere hN μ J β)
  have hmap : Continuous (fun q : ℝ × Vector N => (q.1,U q.2)) :=
    continuous_fst.prodMk (U.continuous.comp continuous_snd)
  exact ((realExpectation_joint_continuous μ J β hf hfc).comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)).mul
      ((realExpectation_joint_continuous μ (rotatedDisorder U J) β hg hgc).comp hmap)

lemma rotationInterpolation_hasDerivAt_zero (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t z : ℝ) (hz : 0 < z) (hzt : z < t) :
    HasDerivAt (rotationInterpolation μ J β U f g t) 0 z := by
  let := mixtureGibbsLaw_probability hN μ β J
  let Fv := realExpectation μ J β f
  let Gv := realExpectation μ (rotatedDisorder U J) β g
  let Iv : ℝ → Vector N → ℝ := fun r x => Fv (t-r) x*Gv r (U x)
  let Id : ℝ → Vector N → ℝ := fun r x =>
    -(mixedGenerator μ J β (Fv (t-r)) x)*Gv r (U x)+
      Fv (t-r) x*mixedGenerator μ (rotatedDisorder U J) β (Gv r) (U x)
  have hF : Continuous (Function.uncurry Fv) := realExpectation_joint_continuous μ J β hf hfc
  have hG : Continuous (Function.uncurry Gv) := realExpectation_joint_continuous μ (rotatedDisorder U J) β hg hgc
  have hLF : Continuous (fun q : ℝ × Vector N => mixedGenerator μ J β (Fv q.1) q.2) :=
    realExpectation_generator_joint_continuous μ J β hf hfc
  have hLG : Continuous (fun q : ℝ × Vector N => mixedGenerator μ (rotatedDisorder U J) β (Gv q.1) q.2) :=
    realExpectation_generator_joint_continuous μ (rotatedDisorder U J) β hg hgc
  have hback : Continuous (fun q : ℝ × Vector N => (t-q.1,q.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hrot : Continuous (fun q : ℝ × Vector N => (q.1,U q.2)) :=
    continuous_fst.prodMk (U.continuous.comp continuous_snd)
  have hIv : Continuous (Function.uncurry Iv) := (hF.comp hback).mul (hG.comp hrot)
  have hId : Continuous (Function.uncurry Id) :=
    ((hLF.comp hback).neg.mul (hG.comp hrot)).add ((hF.comp hback).mul (hLG.comp hrot))
  have hd := CompactMeasure.hasDerivAt_integral (mixtureGibbsLaw μ β J)
    {x : Vector N | OnSphere x} (physicalSphere_compact N)
    (mixtureGibbsLaw_onSphere hN μ J β) hIv hId 0 t z hz hzt (by
      intro r hr x hx
      have hdF := (mixedExpectation_backward (by omega) μ J β x hx hf hfc (t-r)
        (sub_pos.mpr hr.2)).comp r ((hasDerivAt_id r).const_sub t)
      have hdG := mixedExpectation_backward (by omega) μ (rotatedDisorder U J) β (U x)
        (onSphere_map U hx) hg hgc r hr.1
      have hdf : HasDerivAt (fun s => Fv (t-s) x) (-mixedGenerator μ J β (Fv (t-r)) x) r := by
        dsimp only [Fv,realExpectation]
        convert hdF using 1 <;> (try simp only [Function.comp_def,mul_neg_one])
        rfl
      exact hdf.mul hdG)
  have hFz : ContDiff ℝ 2 (Fv (t-z)) := realExpectation_contDiff μ J β hf hfc _
  have hGz : ContDiff ℝ 2 (Gv z) := realExpectation_contDiff μ (rotatedDisorder U J) β hg hgc _
  have hcross := crossGenerator_pairing hN μ J β U hFz hGz
  have hi1 : Integrable (fun x => mixedGenerator μ J β (Fv (t-z)) x*Gv z (U x))
      (mixtureGibbsLaw μ β J) := integrable_gibbs_of_continuous hN β
    (fieldOfMixture_contDiff μ J).continuous
    ((Ito.generator_continuous β _ (mixedGradient_contDiff μ J) hFz).mul (hGz.continuous.comp U.continuous))
  have hi2 : Integrable (fun x => Fv (t-z) x*mixedGenerator μ (rotatedDisorder U J) β (Gv z) (U x))
      (mixtureGibbsLaw μ β J) := integrable_gibbs_of_continuous hN β
    (fieldOfMixture_contDiff μ J).continuous
    (hFz.continuous.mul ((Ito.generator_continuous β _ (mixedGradient_contDiff μ (rotatedDisorder U J)) hGz).comp U.continuous))
  have hzero : (∫ x, Id z x ∂mixtureGibbsLaw μ β J)=0 := by
    dsimp [Id]
    simp_rw [neg_mul]
    rw [integral_add (f := fun x => -(mixedGenerator μ J β (Fv (t-z)) x*Gv z (U x)))
      (g := fun x => Fv (t-z) x*mixedGenerator μ (rotatedDisorder U J) β (Gv z) (U x))
      hi1.neg hi2,integral_neg,hcross]
    ring
  rw [hzero] at hd
  exact hd

/-- Cross-field balance for the actual physical transition expectations. -/
theorem compact_rotation_pairing (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ≥0) :
    (∫ x, f x*mixedExpectation μ J β t (fun y => g (U y)) x ∂mixtureGibbsLaw μ β J) =
      ∫ x, f x*mixedExpectation μ (rotatedDisorder U J) β t g (U x) ∂mixtureGibbsLaw μ β J := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
    (rotationInterpolation_continuous hN μ J β U hf hfc hg hgc t).continuousOn
    (fun z hz => rotationInterpolation_hasDerivAt_zero hN μ J β U hf hfc hg hgc t z hz.1 hz.2)
    ((continuous_const : Continuous (fun _ : ℝ => (0:ℝ))).intervalIntegrable 0 t)
  simp only [intervalIntegral.integral_zero,rotationInterpolation,sub_self,sub_zero,realExpectation_zero] at hh
  have he : (∫ x, mixedExpectation μ J β t f x*g (U x) ∂mixtureGibbsLaw μ β J) =
      ∫ x, f x*mixedExpectation μ (rotatedDisorder U J) β t g (U x) ∂mixtureGibbsLaw μ β J := by
    simpa only [realExpectation,Real.toNNReal_coe] using (sub_eq_zero.mp hh.symm).symm
  have hgu : ContDiff ℝ 2 (fun x => g (U x)) := hg.comp U.toContinuousLinearEquiv.contDiff
  have hguC : HasCompactSupport (fun x => g (U x)) :=
    hgc.comp_homeomorph U.toContinuousLinearEquiv.toHomeomorph
  exact (compact_mixedExpectation_reversible hN μ J β hf hfc hgu hguC t).symm.trans he

/-- The actual mixed transition expectation rotates at each physical
initial point. The continuous equality follows from true Gibbs full support. -/
theorem compact_mixedExpectation_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {g : Vector N → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    mixedExpectation μ J β t (fun y => g (U y)) x =
      mixedExpectation μ (rotatedDisorder U J) β t g (U x) := by
  let D : Vector N → ℝ := fun y => mixedExpectation μ J β t (fun z => g (U z)) y-
    mixedExpectation μ (rotatedDisorder U J) β t g (U y)
  have hgu : ContDiff ℝ 2 (fun y => g (U y)) := hg.comp U.toContinuousLinearEquiv.contDiff
  have hguC : HasCompactSupport (fun y => g (U y)) := hgc.comp_homeomorph U.toContinuousLinearEquiv.toHomeomorph
  have hD : ContDiff ℝ 2 D := ((mixedExpectation_regular μ J β hgu hguC).1 t).sub
    (((mixedExpectation_regular μ (rotatedDisorder U J) β hg hgc).1 t).comp U.toContinuousLinearEquiv.contDiff)
  obtain ⟨f,hf,hfc,hagree⟩ := exists_C2_cutoff D hD
  have hpair := compact_rotation_pairing hN μ J β U hf hfc hg hgc t
  have hi1 : Integrable (fun y => f y*mixedExpectation μ J β t (fun z => g (U z)) y)
      (mixtureGibbsLaw μ β J) := integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous
    (hf.continuous.mul ((mixedExpectation_regular μ J β hgu hguC).1 t).continuous)
  have hi2 : Integrable (fun y => f y*mixedExpectation μ (rotatedDisorder U J) β t g (U y))
      (mixtureGibbsLaw μ β J) := integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous
    (hf.continuous.mul (((mixedExpectation_regular μ (rotatedDisorder U J) β hg hgc).1 t).continuous.comp U.continuous))
  have hz : (∫ y, (D y)^2 ∂mixtureGibbsLaw μ β J)=0 := by
    calc
      _ = ∫ y, f y*mixedExpectation μ J β t (fun z => g (U z)) y-
          f y*mixedExpectation μ (rotatedDisorder U J) β t g (U y) ∂mixtureGibbsLaw μ β J := by
        apply integral_congr_ae
        filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with y hy
        rw [(hagree y hy).1]
        dsimp [D]
        ring
      _ = _ := by
        rw [integral_sub (f := fun y => f y*mixedExpectation μ J β t (fun z => g (U z)) y)
          (g := fun y => f y*mixedExpectation μ (rotatedDisorder U J) β t g (U y)) hi1 hi2,hpair]
        ring
  have hiD : Integrable (fun y => (D y)^2) (mixtureGibbsLaw μ β J) :=
    integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous (hD.continuous.pow 2)
  have haeSq := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (D y)) hiD).mp hz
  have hae : D =ᵐ[mixtureGibbsLaw μ β J] 0 := haeSq.mono (fun y hy => sq_eq_zero_iff.mp hy)
  have he := continuous_eq_zero_onSphere_of_gibbs_ae hN β (fieldOfMixture_contDiff μ J).continuous
    hD.continuous hae x hx
  exact sub_eq_zero.mp he

/-- Literal rotation covariance of the genuine mixed Langevin transition
kernel, for every physical initial point and every nonnegative time. -/
theorem mixedTransitionKernel_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    (mixedTransitionKernel μ J β t x).map U =
      mixedTransitionKernel μ (rotatedDisorder U J) β t (U x) := by
  have hsupport : ∀ᵐ y ∂mixedTransitionKernel μ J β t x, OnSphere y := by
    rw [mixedTransitionKernel_apply,mixedTransitionLaw]
    exact (ae_map_iff (mixedProcess_measurable μ J β x t).aemeasurable
      (sphere_measurableSet N)).2
        ((mixedProcess_onSphere (by omega) μ J β x hx).mono fun _ h => h t)
  have hsupportRot : ∀ᵐ y ∂mixedTransitionKernel μ (rotatedDisorder U J) β t (U x), OnSphere y := by
    rw [mixedTransitionKernel_apply,mixedTransitionLaw]
    exact (ae_map_iff (mixedProcess_measurable μ (rotatedDisorder U J) β (U x) t).aemeasurable
      (sphere_measurableSet N)).2
        ((mixedProcess_onSphere (by omega) μ (rotatedDisorder U J) β (U x) (onSphere_map U hx)).mono fun _ h => h t)
  have hmapSupport : ∀ᵐ y ∂(mixedTransitionKernel μ J β t x).map U, OnSphere y := by
    apply (ae_map_iff U.continuous.measurable.aemeasurable (sphere_measurableSet N)).mpr
    exact hsupport.mono fun y hy => onSphere_map U hy
  apply SphericalAging.SphereSmoothTestMeasureExt.measure_eq_of_compactC2_integrals hmapSupport hsupportRot
  intro g hg hgc
  rw [integral_map U.continuous.measurable.aemeasurable hg.continuous.stronglyMeasurable.aestronglyMeasurable,
    ← mixedExpectation_eq_kernel μ J β t (fun y => g (U y)) (hg.continuous.comp U.continuous).stronglyMeasurable x,
    ← mixedExpectation_eq_kernel μ (rotatedDisorder U J) β t g hg.continuous.stronglyMeasurable (U x)]
  exact compact_mixedExpectation_rotation hN μ J β U hg hgc t x hx

end
end SlowEquilibration.SphericalRotationCovariance
