-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetAngularFactorization
public import SlowEquilibration.GaussianCoefficientKernelScalarExpIntegrable

@[expose] public section

/-! The original latitude field is an actual scalar linear observation of
the same tensor coefficient Gaussian posterior used for the Hessian. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression ConditionedDeterminantMoments
open SphericalSequentialRegression IntrinsicHessianLaw
open GaussianCoefficientKernelScalarExpIntegrable
set_option autoImplicit false

theorem originalLatitudeBankPoint_physicalMixedPalm_integrable
    {d : ℕ} (μ : FiniteMixture) (Q a β : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) (y : Vector (d+1)) :
    Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      originalLatitudeBankPoint μ a β u J y)
      (mixedLaw μ Q u hu mark) := by
  let σ := originalLatitudePoint a u (quadraticBankDirection (d+1) u y)
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let B := flatJetCLM (mixtureCoefficients μ) 0 σ (fun i => Fin.elim0 i)
  let w := jointScoreTarget (d+1) (((d+2:ℕ):ℝ) • mark)
  have h := coefficientKernel_scalar_exp_integrable A B w β
  change Integrable (fun J => Real.exp (β*actualObservation B J))
    (mixedLaw μ Q u hu mark) at h
  convert h using 1
  funext J
  have hB : actualObservation B J = field (mixtureCoefficients μ) J σ := by
    simp only [B,actualObservation,flatJetCLM_apply,unpack_euclideanDisorder]
    simp [jet]
  rw [hB]
  rfl

/-- Any square-integrable determinant has an integrable product with each
original latitude exponential, since the exponential itself has every
finite Gaussian moment under the literal coefficient posterior. -/
theorem originalLatitudeBankPoint_det_integrable_of_det_sq
    {d : ℕ} (μ : FiniteMixture) (Q a β : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2))
    (hDsq : Integrable (fun J => (intrinsicDet μ Q u J)^2)
      (mixedLaw μ Q u hu mark))
    (y : Vector (d+1)) :
    Integrable (fun J => intrinsicDet μ Q u J *
      originalLatitudeBankPoint μ a β u J y)
      (mixedLaw μ Q u hu mark) := by
  let ν := mixedLaw μ Q u hu mark
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
    have hh := originalLatitudeBankPoint_physicalMixedPalm_integrable
      μ Q a (2*β) u hu mark y
    convert hh using 1
    funext J
    dsimp [F,originalLatitudeBankPoint]
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hFlp : MemLp F 2 ν :=
    (memLp_two_iff_integrable_sq hFmeas.aestronglyMeasurable).mpr hF2
  exact hDlp.integrable_mul hFlp

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
