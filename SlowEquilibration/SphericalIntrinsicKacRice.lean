-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.RoundSphereChartIntegral
public import SlowEquilibration.SphericalKacRiceGluing
public import SlowEquilibration.IntrinsicGradientRegression
public import SlowEquilibration.SphericalIntrinsicHessianJet

/-!
# Global intrinsic marked Kac--Rice for the actual mixed spherical field

All quantities are the actual tensor field, its actual intrinsic gradient and
Hessian, the independently constructed ordinary round volume, and the canonical
full-tensor Gaussian regression law at literal gradient zero. Arbitrary Borel
marks may depend on the entire original tensor disorder. The omitted chart pole
is proved almost surely noncritical from the actual positive-dimensional
gradient density, and its round volume is proved zero independently.
-/

@[expose] public section

namespace SlowEquilibration.SphericalIntrinsicKacRice

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphereHessian SlowEquilibration.SphericalKacRiceGluing
open SlowEquilibration.SphericalIntrinsicChartKacRice
open SlowEquilibration.IntrinsicGradientRegression
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

/-- Every fixed point of the positive-dimensional actual sphere is almost
surely noncritical, derived from the genuine intrinsic gradient density. -/
theorem fixed_point_noncritical_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) :
    ∀ᵐ J ∂disorderLaw (n + 1) μ.maxDegree,
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) x ≠ 0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  letI : Nontrivial (tangentPlane x) := Module.nontrivial_of_finrank_pos
    (by rw [tangentPlane_finrank x hx]; omega)
  have hlaw := actualObservation_has_explicit_density (intrinsicGamma c x)
    (center_intrinsicGamma_surjective (by omega) μ hQ x hx)
  have hobs : ∀ᵐ J ∂disorderLaw (n + 1) μ.maxDegree,
      actualObservation (intrinsicGamma c x) J ≠ 0 := by
    rw [ae_iff]
    have hz := hlaw.measure_eq (p := fun y => y = 0) (measurableSet_singleton 0)
    simpa only [not_not, Set.setOf_eq_eq_singleton, measure_singleton] using hz
  filter_upwards [hobs] with J hJ
  intro hcrit
  apply hJ
  apply Subtype.ext
  change (intrinsicGamma c x (euclideanDisorder J) : Vector (n + 1)) = 0
  rw [intrinsicGamma_coe (by omega) c x hx, unpack_euclideanDisorder]
  exact hcrit

/-- Genuine global intrinsic marked Kac--Rice, under the original tensor
disorder law and with its canonical full-field conditional law at zero.
Every geometric, density, and pole-removal hypothesis is proved from the
actual positive-overlap finite mixture. -/
theorem actual_sphere_marked_kacRice (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n + 1) μ.maxDegree → Vector (n + 1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n + 1) μ.maxDegree × Vector (n + 1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualSphereCount n c psi) (disorderLaw (n + 1) μ.maxDegree) ∧
    (∫⁻ J, actualSphereCount n c psi J ∂disorderLaw (n + 1) μ.maxDegree) =
      ∫⁻ x, GaussianRegression.observationPdf (intrinsicGamma c x) 0 *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂coefficientKernel (intrinsicGamma c x) 0 ∂manuscriptRoundVolume n := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F : Vector (n + 1) → ℝ≥0∞ := fun x =>
    GaussianRegression.observationPdf (intrinsicGamma c x) 0 *
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
        ∂coefficientKernel (intrinsicGamma c x) 0
  have hm : Measurable fun p : Disorder (n + 1) μ.maxDegree × EuclideanSpace ℝ (Fin n) =>
      psi p.1 (manuscriptChart n p.2) := hpsi.comp
    (measurable_fst.prodMk ((RoundSphereChartIntegral.manuscriptChart_continuous n).measurable.comp measurable_snd))
  have hk := actual_tensor_chart_round_kacRice n μ hQ
    (fun J u => psi J (manuscriptChart n u)) hm
  have hpole := fixed_point_noncritical_ae n hn μ hQ (southPole n) (southPole_norm_sq n)
  have hcount := actualSphereCount_ae_eq_chart n c psi hpole
  refine ⟨hk.1.congr hcount.symm, (lintegral_congr_ae hcount).trans (hk.2.trans ?_)⟩
  have hround := RoundSphereChartIntegral.manuscriptRoundVolume_lintegral_chart n F
  rw [manuscriptRoundVolume_restrict_full_chart n hn] at hround
  change _ = ∫⁻ x, F x ∂manuscriptRoundVolume n
  rw [hround]
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro u hu
  have hu' : ‖u‖ < 2 := by simpa using hu
  dsimp only [F, c]
  rw [chart_coefficientKernel_zero_eq μ hQ hu',
    center_intrinsic_pdf_zero μ hQ.le _ (manuscriptChart_norm_sq hu')]
  simp only [intrinsicGradientDensity, mul_assoc, mul_left_comm]

/-- The same genuine global marked formula with the constant isotropic
intrinsic gradient density evaluated explicitly. -/
theorem actual_sphere_marked_kacRice_explicit (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n + 1) μ.maxDegree → Vector (n + 1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n + 1) μ.maxDegree × Vector (n + 1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualSphereCount n c psi J ∂disorderLaw (n + 1) μ.maxDegree) =
      intrinsicGradientDensity n μ Q *
        ∫⁻ x, ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂coefficientKernel (intrinsicGamma c x) 0 ∂manuscriptRoundVolume n := by
  dsimp only
  rw [(actual_sphere_marked_kacRice n hn μ hQ psi hpsi).2,
    ← lintegral_const_mul' _ _ (show intrinsicGradientDensity n μ Q ≠ ⊤ from ENNReal.ofReal_ne_top)]
  apply lintegral_congr_ae
  filter_upwards [manuscriptRoundVolume_onSphere n] with x hx
  rw [center_intrinsic_pdf_zero μ hQ.le x hx]
  rfl

end
end SlowEquilibration.SphericalIntrinsicKacRice
