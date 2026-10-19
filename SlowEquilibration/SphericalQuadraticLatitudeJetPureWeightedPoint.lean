-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureBankDeterminantCauchy
public import SlowEquilibration.SphericalQuadraticLatitudeJetPhysicalWeightedPoint

@[expose] public section

/-! Pointwise L¹ bounds for the literal original latitude exponential with
the actual conditioned pure Hessian determinant. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter SphericalModel SphericalGaussianJet
open WholeFieldRegression ConditionedDeterminantMoments
open SphericalSequentialRegression IntrinsicHessianLaw ValueTangentConditioning
open GaussianCoefficientKernelScalarExpIntegrable
open SphericalTAPPurePalmDeterminantQuadraticReduction
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem originalLatitudeBankPoint_physicalPurePalm_integrable
    {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q a β : ℝ) (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) (y : Vector (d+1)) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      originalLatitudeBankPoint μ a β u J y)
      (pureLaw p hp alpha halpha Q u hu e) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let σ := originalLatitudePoint a u (quadraticBankDirection (d+1) u y)
  let A := valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let B := flatJetCLM (mixtureCoefficients μ) 0 σ (fun i => Fin.elim0 i)
  let w := jointValueTarget (d+1) (((d+2:ℕ):ℝ)*e)
  have h := coefficientKernel_scalar_exp_integrable A B w β
  change Integrable (fun J => Real.exp (β*actualObservation B J))
    (pureLaw p hp alpha halpha Q u hu e) at h
  convert h using 1
  funext J
  have hB : actualObservation B J = field (mixtureCoefficients μ) J σ := by
    simp only [B,actualObservation,flatJetCLM_apply,unpack_euclideanDisorder]
    simp [jet]
  rw [hB]
  rfl

theorem originalLatitudeBankPoint_det_integrable_pure_of_det_sq
    {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q a β : ℝ) (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ)
    (hDsq : Integrable (fun J =>
      (intrinsicDet (FiniteMixture.pure p hp alpha halpha) Q u J)^2)
      (pureLaw p hp alpha halpha Q u hu e))
    (y : Vector (d+1)) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Integrable (fun J => intrinsicDet μ Q u J *
      originalLatitudeBankPoint μ a β u J y)
      (pureLaw p hp alpha halpha Q u hu e) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let D := intrinsicDet μ Q u
  let F := fun J => originalLatitudeBankPoint μ a β u J y
  have hDmeas : Measurable D := by
    unfold D intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hFmeas : Measurable F := by
    have hf := originalLatitudeBankPoint_joint_measurable μ a β u
    simpa only [F,Function.comp_def,Prod.fst,Prod.snd,id_eq] using
      hf.comp (measurable_id.prodMk measurable_const)
  have hDlp : MemLp D 2 ν :=
    (memLp_two_iff_integrable_sq hDmeas.aestronglyMeasurable).mpr hDsq
  have hF2 : Integrable (fun J => (F J)^2) ν := by
    have hh := originalLatitudeBankPoint_physicalPurePalm_integrable
      p hp alpha halpha Q a (2*β) u hu e y
    convert hh using 1
    funext J
    dsimp [F,originalLatitudeBankPoint]
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hFlp : MemLp F 2 ν :=
    (memLp_two_iff_integrable_sq hFmeas.aestronglyMeasurable).mpr hF2
  exact hDlp.integrable_mul hFlp

theorem intrinsicDet_physicalPurePalm_sq_integrable_eventually
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᶠ d : ℕ in atTop,
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (e : ℝ),
        2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*e →
        Integrable (fun J => (intrinsicDet μ Q u J)^2)
          (pureLaw p hp alpha halpha Q u hu e) := by
  have hdet := pure_conditioned_determinant_moments_sharp_eventually
    p hp alpha halpha hQ hg
  filter_upwards [hdet] with d hd
  intro u hu e he
  obtain ⟨_,_,hm,hDint,_⟩ := hd u hu e he 2 (by norm_num)
  simp only [Real.rpow_two] at hDint
  let μ := FiniteMixture.pure p hp alpha halpha
  let m := ∫ J, intrinsicDet μ Q u J
    ∂pureLaw p hp alpha halpha Q u hu e
  have hm' : m ≠ 0 := (ne_of_gt hm)
  convert hDint.const_mul (m^2) using 1
  funext J
  change (intrinsicDet μ Q u J)^2 = m^2*(intrinsicDet μ Q u J/m)^2
  field_simp [hm']

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
