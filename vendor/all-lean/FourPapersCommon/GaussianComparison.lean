module
public import FourPapersCommon.GaussianInterpolation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Covariance comparison for genuine, centered finite Gaussian energy vectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass Filter Set
open scoped BigOperators Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

theorem gaussianSmartPath_covariance (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] EnergySpace N)
    (hcross : ∀ σ τ : Config N, (∫ ω, A (g ω) σ * B (g ω) τ) = 0)
    (t : ℝ) (σ τ : Config N) :
    (∫ ω, gaussianSmartPath A B t (g ω) σ * gaussianSmartPathDeriv A B t (g ω) τ) =
      Real.sin t * Real.cos t *
        ((∫ ω, B (g ω) σ * B (g ω) τ) - (∫ ω, A (g ω) σ * A (g ω) τ)) := by
  have hcross' (σ τ : Config N) : (∫ ω, B (g ω) σ * A (g ω) τ) = 0 := by
    simpa only [mul_comm] using hcross τ σ
  rw [gaussianLinearImage_secondMoment g hg]
  change gaussianSpectralCovariance (fun i => (hg.τ i : ℝ))
    (fun i => Real.cos t • A (hg.w i) + Real.sin t • B (hg.w i))
    (fun i => -Real.sin t • A (hg.w i) + Real.cos t • B (hg.w i)) σ τ = _
  rw [gaussianSpectralCovariance_linearCombination]
  simp only [gaussianSpectralCovariance]
  rw [← gaussianLinearImage_secondMoment g hg A A,
    ← gaussianLinearImage_secondMoment g hg A B,
    ← gaussianLinearImage_secondMoment g hg B A,
    ← gaussianLinearImage_secondMoment g hg B B, hcross, hcross']
  ring

theorem hasDerivAt_gaussianSmartPath_covariance (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] EnergySpace N)
    (hcross : ∀ σ τ : Config N, (∫ ω, A (g ω) σ * B (g ω) τ) = 0)
    (field : EnergySpace N) (t : ℝ) :
    HasDerivAt
      (fun s => ∫ ω, free_energy_density (N := N) (gaussianSmartPath A B s (g ω) + field))
      (Real.sin t * Real.cos t * ∫ ω, ∑ σ : Config N, ∑ τ : Config N,
        ((∫ η, B (g η) σ * B (g η) τ) - (∫ η, A (g η) σ * A (g η) τ)) *
        hessian_free_energy N (gaussianSmartPath A B t (g ω) + field)
          (std_basis N σ) (std_basis N τ)) t := by
  classical
  haveI : FiniteDimensional ℝ E := hg.w.toBasis.finiteDimensional_of_finite
  have hd := hasDerivAt_integral_gaussianSmartPath
    (SpinGlass.GeneralizedLatala.gaussianHilbert_hasGaussianLaw hg).integrable A B field t
  rw [gaussianFreeEnergy_ibp_linear g hg] at hd
  convert hd using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  rw [gaussianFreeEnergy_trace_covariance g hg]
  simp_rw [gaussianSmartPath_covariance g hg A B hcross,
    Finset.mul_sum, ← mul_assoc]

theorem gaussianFreeEnergy_covariance_comparison (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] EnergySpace N)
    (hcross : ∀ σ τ : Config N, (∫ ω, A (g ω) σ * B (g ω) τ) = 0)
    (hdiag : ∀ σ : Config N, (∫ ω, A (g ω) σ * A (g ω) σ) =
      ∫ ω, B (g ω) σ * B (g ω) σ)
    (hcov : ∀ σ τ : Config N, (∫ ω, A (g ω) σ * A (g ω) τ) ≤
      ∫ ω, B (g ω) σ * B (g ω) τ)
    (field : EnergySpace N) :
    (∫ ω, free_energy_density (N := N) (B (g ω) + field)) ≤
      ∫ ω, free_energy_density (N := N) (A (g ω) + field) := by
  classical
  let F : ℝ → ℝ := fun t => ∫ ω, free_energy_density (N := N)
    (gaussianSmartPath A B t (g ω) + field)
  have hderiv (t : ℝ) := hasDerivAt_gaussianSmartPath_covariance g hg A B hcross field t
  have hcts : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hderiv t).continuousAt)
  have hanti : AntitoneOn F (Icc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcts.continuousOn
    · intro t _
      exact (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
        (by linarith [ht.2, Real.pi_pos])
      have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [ht.1, Real.pi_pos]) ht.2.le
      apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsin hcos)
      apply integral_nonpos
      intro ω
      apply gaussianFreeEnergy_covariance_contraction_nonpos
      · intro σ
        simp [hdiag σ]
      · intro σ τ
        exact sub_nonneg.mpr (hcov σ τ)
  have hh := hanti (show (0 : ℝ) ∈ Icc 0 (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show Real.pi / 2 ∈ Icc 0 (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simpa [F, gaussianSmartPath] using hh

end FourPapersCommon
