-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalScoreDensity
public import SlowEquilibration.SphericalFiniteCritical
public import SlowEquilibration.SphericalGibbs

/-! Actual score-window counts and uniform-sphere normalization. -/

@[expose] public section

namespace SlowEquilibration.SphericalMarkedWindows

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.GaussianRegression
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.SphericalForm
open SlowEquilibration.SphereHessian SlowEquilibration.SphereChartVolume
open SlowEquilibration.SphericalKacRiceGluing SlowEquilibration.SphericalMorse
open SlowEquilibration.SphericalIntrinsicChartKacRice SlowEquilibration.SphericalIntrinsicKacRice
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal normalized value and radial derivative of the actual field. -/
def actualScore {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) :
    EuclideanSpace ℝ (Fin 2) := (N : ℝ)⁻¹ • scoreCLM c x (euclideanDisorder J)

theorem actualScore_jointContinuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (fun p : Disorder N P × Vector N => actualScore c p.1 p.2) := by
  have hraw : Continuous (fun p : Disorder N P × Vector N => scoreCLM c p.2 (euclideanDisorder p.1)) := by
    change Continuous ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
      (fun p : Disorder N P × Vector N => fun i => scoreCLM c p.2 (euclideanDisorder p.1) i))
    apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : Disorder N P × Vector N => scoreCLM c p.2 (euclideanDisorder p.1) 0)
      simp only [scoreCLM_apply_zero, unpack_euclideanDisorder]
      exact field_jointContinuous c
    · change Continuous (fun p : Disorder N P × Vector N => scoreCLM c p.2 (euclideanDisorder p.1) 1)
      simp only [scoreCLM_apply_one, unpack_euclideanDisorder, radial_jet_sum]
      unfold blockField SphericalAging.FiniteModel.Hamiltonian SphericalAging.FiniteModel.tensorMonomial
      fun_prop
  exact hraw.const_smul ((N : ℝ)⁻¹)

/-- A literal sum over the intrinsic critical points lying in the score window. -/
def actualScoreWindowCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' x : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
    surfaceGradient (field c J) x = 0 ∧ actualScore c J x ∈ K}, psi J x

theorem actualScoreWindowCount_eq_indicator {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+1) P) :
    actualScoreWindowCount n c K psi J =
      actualSphereCount n c (fun J x => if actualScore c J x ∈ K then psi J x else 0) J := by
  classical
  unfold actualScoreWindowCount actualSphereCount
  dsimp only
  rw [tsum_subtype]
  rw [tsum_subtype (f := fun x : Vector (n+1) =>
    if actualScore c J x ∈ K then psi J x else 0)]
  apply tsum_congr
  intro x
  by_cases hx : ‖x‖ ^ 2 = (n+1 : ℕ) <;>
    by_cases hg : surfaceGradient (field c J) x = 0 <;>
    by_cases hk : actualScore c J x ∈ K <;>
    simp only [Nat.cast_add, Nat.cast_one] at hx <;> simp [hx, hg, hk]

theorem scoreWindowMark_measurable {N P : ℕ} (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder N P → Vector N → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder N P × Vector N => psi p.1 p.2) :
    Measurable (fun p : Disorder N P × Vector N =>
      if actualScore c p.1 p.2 ∈ K then psi p.1 p.2 else 0) :=
  Measurable.ite (hK.preimage (actualScore_jointContinuous c).measurable) hpsi measurable_const

/-- The actual intrinsic determinant is a Borel function of the entire
disorder at each genuine sphere point. -/
theorem intrinsicDet_measurable {n P : ℕ} (c : Degree P → ℝ) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    Measurable (fun J : Disorder (n+1) P => ENNReal.ofReal |(intrinsicHessian (field c J) x).det|) := by
  have hm : Continuous (hessianMatrix c x (tangentFrame x hx)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    convert (jetCLM c 2 x ![tangentFrame x hx i, tangentFrame x hx j]).continuous using 1
    funext J
    exact (jetCLM_apply c 2 x ![tangentFrame x hx i, tangentFrame x hx j] J).symm
  have hr : Continuous (fun J : Disorder (n+1) P => jet c 1 x (fun _ => x) J / (n+1 : ℕ)) :=
    by simpa only [jetCLM_apply] using
      (jetCLM c 1 x (fun _ => x)).continuous.div_const ((n+1 : ℕ) : ℝ)
  have h := (hm.sub (hr.smul (continuous_const (y := (1 : Matrix (Fin n) (Fin n) ℝ))))).matrix_det.abs.measurable.ennreal_ofReal
  convert h using 1
  funext J
  rw [IntrinsicHessianLaw.intrinsicHessian_det c J x hx]
  rfl

theorem manuscriptRoundVolume_mass_ne_zero (n : ℕ) : manuscriptRoundVolume n univ ≠ 0 := by
  rw [manuscriptRoundVolume_total]
  exact mul_ne_zero (radiusAreaScale_ne_zero n) SphereVolume.angular_total_ne_zero

theorem manuscriptRoundVolume_mass_ne_top (n : ℕ) : manuscriptRoundVolume n univ ≠ ⊤ := by
  rw [manuscriptRoundVolume_total]
  exact ENNReal.mul_ne_top (radiusAreaScale_ne_top n) (measure_ne_top _ _)

/-- Genuine round Riemannian volume is its total area times the actual
Gaussian-direction uniform sphere probability law. -/
theorem manuscriptRoundVolume_eq_area_sphereLaw (n : ℕ) :
    manuscriptRoundVolume n = manuscriptRoundVolume n univ • sphereLaw (n+1) := by
  change manuscriptRoundVolume n = manuscriptRoundVolume n univ •
    SphericalAging.SphereInitialLaw.sphereLaw (n+1)
  rw [sphereLaw_eq_normalized_roundVolume, smul_smul,
    ENNReal.mul_inv_cancel (manuscriptRoundVolume_mass_ne_zero n)
      (manuscriptRoundVolume_mass_ne_top n), one_smul]

/-- The physical round-area times zero-gradient-density prefactor. -/
def sphereKRPrefactor (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ≥0∞ :=
  manuscriptRoundVolume n univ * intrinsicGradientDensity n μ Q

theorem intrinsicGradientDensity_physical (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    intrinsicGradientDensity n μ Q =
      ENNReal.ofReal ((2 * Real.pi * (Q * μ.xi1 Q)) ^ (-(n : ℝ) / 2)) := by
  have ha : 0 ≤ Q * μ.xi1 Q := (mul_pos hQ (mixture_xi1_pos μ hQ)).le
  have hp : 0 ≤ 2 * Real.pi := by positivity
  have hs : Real.sqrt ((Q * μ.xi1 Q) ^ n) = (Q * μ.xi1 Q) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul ha]
    congr 1
    ring
  unfold intrinsicGradientDensity GaussianDensity.normalizer
  rw [hs]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    Real.rpow_neg (mul_nonneg hp ha), Real.mul_rpow hp ha, mul_inv]
  rfl

theorem sphereKRPrefactor_physical (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    sphereKRPrefactor n μ Q = manuscriptRoundVolume n univ *
      ENNReal.ofReal ((2 * Real.pi * (Q * μ.xi1 Q)) ^ (-(n : ℝ) / 2)) := by
  rw [sphereKRPrefactor, intrinsicGradientDensity_physical n μ hQ]

theorem actual_sphere_marked_kacRice_uniform (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualSphereCount n c psi J ∂disorderLaw (n+1) μ.maxDegree) =
      sphereKRPrefactor n μ Q *
        ∫⁻ x, ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂coefficientKernel (intrinsicGamma c x) 0 ∂sphereLaw (n+1) := by
  dsimp only
  rw [actual_sphere_marked_kacRice_explicit n hn μ hQ psi hpsi,
    manuscriptRoundVolume_eq_area_sphereLaw, lintegral_smul_measure]
  simp only [sphereKRPrefactor, smul_eq_mul, mul_assoc, mul_left_comm]

end
end SlowEquilibration.SphericalMarkedWindows
