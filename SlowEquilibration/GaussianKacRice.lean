-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianBlockFiber
public import SlowEquilibration.CoefficientKacRice

/-!
# Local marked Gaussian Kac--Rice with its canonical zero-fiber kernel

The genuine C1 coefficient-incidence area formula is converted to the literal
zero-observation Gaussian kernel using the proved coefficient graph Jacobian.
The mark retains arbitrary Borel dependence on the full coefficient vector.
-/

@[expose] public section

namespace SlowEquilibration.GaussianKacRice

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianBlockFiber
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The genuine standard Gaussian coefficient law in the ordinary block coordinates. -/
def splitGaussian : Measure (U × V) := (stdGaussian (Coeff U V)).map WithLp.ofLp

/-- Its actual ordinary Gaussian density, transported from the Hilbert coefficient space. -/
def splitPdf (z : U × V) : ℝ≥0∞ := ENNReal.ofReal (GaussianDensity.density (WithLp.toLp 2 z))

lemma splitPdf_measurable : Measurable (splitPdf (U := U) (V := V)) := by
  exact (GaussianDensity.density_continuous.comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm.continuous).measurable.ennreal_ofReal

/-- Explicit density of the actual split Gaussian law, proved by genuine
volume-preserving unflattening rather than a chosen Radon--Nikodym representative. -/
theorem splitGaussian_density : splitGaussian (U := U) (V := V) =
    ((volume : Measure U).prod (volume : Measure V)).withDensity splitPdf := by
  unfold splitGaussian
  rw [GaussianDensity.stdGaussian_eq_withDensity]
  have h := GaussianRegression.map_withDensity_equiv (MeasurableEquiv.toLp 2 (U × V)).symm
    (volume : Measure (Coeff U V))
    (fun z => ENNReal.ofReal (GaussianDensity.density z))
    GaussianDensity.density_continuous.measurable.ennreal_ofReal
  change ((volume : Measure (Coeff U V)).withDensity _).map WithLp.ofLp = _ at h
  rw [h]
  change ((volume : Measure (Coeff U V)).map WithLp.ofLp).withDensity splitPdf = _
  rw [(WithLp.volume_preserving_ofLp U V).map_eq]
  rfl

/-- The actual gradient observation at one spatial point. -/
def observationAt (G1 : U → U →L[ℝ] U) (G2 : U → V →L[ℝ] U) (u : U) :
    Coeff U V →L[ℝ] U :=
  (G1 u).comp (WithLp.fstL 2 ℝ U V) + (G2 u).comp (WithLp.sndL 2 ℝ U V)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem observationAt_apply (G1 : U → U →L[ℝ] U) (G2 : U → V →L[ℝ] U)
    (u : U) (z : Coeff U V) :
    observationAt G1 G2 u z = CoefficientKacRice.gradient G1 G2 z.ofLp u := rfl

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace V] [BorelSpace V] in
lemma coordinateHessian_eq_at (G1 : U → U →L[ℝ] U) (G2 : U → V →L[ℝ] U)
    (u : U) (h1 : DifferentiableAt ℝ G1 u) (h2 : DifferentiableAt ℝ G2 u) (z : U × V) :
    CoefficientKacRice.coordinateHessian G1 G2 z u =
      (fderiv ℝ G1 u).flip z.1 + (fderiv ℝ G2 u).flip z.2 := by
  have hd := (h1.hasFDerivAt.clm_apply (hasFDerivAt_const z.1 u)).add
    (h2.hasFDerivAt.clm_apply (hasFDerivAt_const z.2 u))
  have he : CoefficientKacRice.gradient G1 G2 z =
      ((fun y => G1 y z.1) + fun y => G2 y z.2) := by funext y; rfl
  unfold CoefficientKacRice.coordinateHessian
  rw [he]
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using hd.fderiv

omit [FiniteDimensional ℝ U] in
lemma hessian_mark_measurable (G1 : U → U →L[ℝ] U) (G2 : U → V →L[ℝ] U)
    (u : U) (h1 : DifferentiableAt ℝ G1 u) (h2 : DifferentiableAt ℝ G2 u)
    (phi : (U × V) → U → ℝ≥0∞) (hphi : Measurable fun p : (U × V) × U => phi p.1 p.2) :
    Measurable (fun z : Coeff U V =>
      ENNReal.ofReal |(CoefficientKacRice.coordinateHessian G1 G2 z.ofLp u).det| * phi z.ofLp u) := by
  have hc : Continuous (fun z : U × V => CoefficientKacRice.coordinateHessian G1 G2 z u) := by
    simp_rw [coordinateHessian_eq_at G1 G2 u h1 h2]
    exact ((fderiv ℝ G1 u).flip.continuous.comp continuous_fst).add
      ((fderiv ℝ G2 u).flip.continuous.comp continuous_snd)
  exact ((ContinuousLinearMap.continuous_det.comp (hc.comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V).continuous)).abs.measurable.ennreal_ofReal).mul
    (hphi.comp ((WithLp.prodContinuousLinearEquiv 2 ℝ U V).continuous.measurable.prodMk measurable_const))

/-- The genuine local marked Gaussian Kac--Rice identity. The conditional
kernel is derived for every target, and the displayed target is literal gradient
zero. The mark may depend on every coefficient and may have infinite integral. -/
theorem local_marked_kacRice
    (G1 : U → U →L[ℝ] U) (G2 : U → V →L[ℝ] U)
    (s : Set U) (hs : IsOpen s) (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (phi : (U × V) → U → ℝ≥0∞) (hphi : Measurable fun p : (U × V) × U => phi p.1 p.2) :
    (∫⁻ z, CoefficientKacRice.gradientCount G1 G2 s phi z ∂splitGaussian) =
      ∫⁻ u in s, GaussianRegression.observationPdf (observationAt G1 G2 u) 0 *
        ∫⁻ z, ENNReal.ofReal |(CoefficientKacRice.coordinateHessian G1 G2 z.ofLp u).det| *
          phi z.ofLp u ∂GaussianRegression.regressionKernel (observationAt G1 G2 u) 0 := by
  rw [splitGaussian_density,
    CoefficientKacRice.local_hessian_density_formula_iterated volume volume G1 G2 s hs h1 h2 hinv
      splitPdf splitPdf_measurable phi hphi]
  apply setLIntegral_congr_fun hs.measurableSet
  intro u hu
  dsimp only
  rcases hinv u hu with ⟨G, hG⟩
  have hm := hessian_mark_measurable G1 G2 u
    ((h1.contDiffAt (hs.mem_nhds hu)).differentiableAt_one)
    ((h2.contDiffAt (hs.mem_nhds hu)).differentiableAt_one) phi hphi
  have he : observationAt G1 G2 u = observation G (G2 u) := by
    simp only [observationAt, observation, hG]
  rw [he]
  have hf := graph_weighted_zero_fiber_integral G (G2 u)
    (fun z : Coeff U V => ENNReal.ofReal
      |(CoefficientKacRice.coordinateHessian G1 G2 z.ofLp u).det| * phi z.ofLp u) hm
  have hp (v : V) : (graph G (G2 u) v).ofLp =
      CoefficientKacRice.incidence (CoefficientKacRice.alpha G1 G2) (u, v) := by
    simp only [graph_apply, WithLp.ofLp_toLp, CoefficientKacRice.incidence,
      CoefficientKacRice.alpha, ← hG, ContinuousLinearMap.inverse_equiv,
      ContinuousLinearEquiv.coe_coe]
  have hp' (v : V) : graph G (G2 u) v =
      WithLp.toLp 2 (CoefficientKacRice.incidence (CoefficientKacRice.alpha G1 G2) (u, v)) := by
    rw [← hp]
  rw [← hf]
  apply lintegral_congr
  intro v
  rw [hp, hp']
  simp only [splitPdf, div_eq_mul_inv, ENNReal.ofReal_mul (abs_nonneg _),
    ← hG]
  have hg : 0 < |(G : U →L[ℝ] U).det| := abs_pos.mpr G.toLinearEquiv.isUnit_det'.ne_zero
  rw [ENNReal.ofReal_inv_of_pos hg]
  ac_rfl

end
end SlowEquilibration.GaussianKacRice
