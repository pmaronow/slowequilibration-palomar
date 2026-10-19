module

public import SlowEquilibration.SpectralCounting
public import SlowEquilibration.FrameParseval
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic

@[expose] public section

/-!
# Measure-space upper frame bound and spectral counting

This file develops the genuine parameter-integral argument of manuscript
Lemma `lem:sp-frame`. It uses actual measures, measurable trial functions,
weighted integral Cauchy--Schwarz, and product-measure integration.
-/

namespace SlowEquilibration

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

/-- A nonnegative integrable density with a finite weighted second moment
has an integrable weighted first moment. -/
theorem weighted_product_integrable {X : Type*} [MeasurableSpace X]
    (π : Measure X) (w φ : X → ℝ) (hw : ∀ᵐ x ∂π, 0 ≤ w x)
    (hwInt : Integrable w π) (hφ : AEStronglyMeasurable φ π)
    (hsquare : Integrable (fun x => w x * (φ x) ^ 2) π) :
    Integrable (fun x => w x * φ x) π := by
  apply (hwInt.add hsquare).mono' (hwInt.aestronglyMeasurable.mul hφ)
  filter_upwards [hw] with x hx
  change ‖w x * φ x‖ ≤ w x + w x * (φ x) ^ 2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
  have hφbound : |φ x| ≤ 1 + (φ x) ^ 2 := by
    nlinarith [sq_nonneg (|φ x| - 1), sq_abs (φ x), abs_nonneg (φ x)]
  have hmul := mul_le_mul_of_nonneg_left hφbound hx
  nlinarith

/-- Cauchy--Schwarz for the genuine measure `w dπ`, expressed using finite
real integrals. The finite weighted second moment is explicit, so no
divergent Bochner integral can be silently replaced by zero. -/
theorem integral_weighted_cauchy {X : Type*} [MeasurableSpace X]
    (π : Measure X) (w φ : X → ℝ) (hw : ∀ᵐ x ∂π, 0 ≤ w x)
    (hwInt : Integrable w π) (hφ : AEStronglyMeasurable φ π)
    (hsquare : Integrable (fun x => w x * (φ x) ^ 2) π) :
    (∫ x, w x * φ x ∂π) ^ 2 ≤
      (∫ x, w x ∂π) * (∫ x, w x * (φ x) ^ 2 ∂π) := by
  have hprod := weighted_product_integrable π w φ hw hwInt hφ hsquare
  have hA : 0 ≤ ∫ x, w x ∂π := integral_nonneg_of_ae hw
  by_cases hAzero : (∫ x, w x ∂π) = 0
  · have hwzero : ∀ᵐ x ∂π, w x = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hw hwInt).mp hAzero
    have hBzero : (∫ x, w x * φ x ∂π) = 0 := by
      calc
        _ = ∫ _x, (0 : ℝ) ∂π := integral_congr_ae (by
          filter_upwards [hwzero] with x hx
          simp [hx])
        _ = 0 := by simp
    simp [hAzero, hBzero]
  · have hApos : 0 < ∫ x, w x ∂π := lt_of_le_of_ne hA (Ne.symm hAzero)
    let a : ℝ := (∫ x, w x * φ x ∂π) / (∫ x, w x ∂π)
    have hpoly : (fun x => w x * (a - φ x) ^ 2) =
        (fun x => a ^ 2 * w x - (2 * a) * (w x * φ x) + w x * (φ x) ^ 2) := by
      funext x
      ring
    have hquad : 0 ≤ a ^ 2 * (∫ x, w x ∂π) -
        (2 * a) * (∫ x, w x * φ x ∂π) + (∫ x, w x * (φ x) ^ 2 ∂π) := by
      have hnon : 0 ≤ ∫ x, w x * (a - φ x) ^ 2 ∂π :=
        integral_nonneg_of_ae (by
          filter_upwards [hw] with x hx
          exact mul_nonneg hx (sq_nonneg _))
      have hlinInt : Integrable (fun x => a ^ 2 * w x - (2 * a) * (w x * φ x)) π :=
        (hwInt.const_mul (a ^ 2)).sub (hprod.const_mul (2 * a))
      rw [hpoly, integral_add (f := fun x => a ^ 2 * w x - (2 * a) * (w x * φ x))
        (g := fun x => w x * (φ x) ^ 2) hlinInt hsquare,
        integral_sub (f := fun x => a ^ 2 * w x) (g := fun x => (2 * a) * (w x * φ x))
        (hwInt.const_mul _) (hprod.const_mul _),
        integral_const_mul, integral_const_mul] at hnon
      exact hnon
    have hmul := mul_nonneg hA hquad
    have hidentity : (∫ x, w x ∂π) *
        (a ^ 2 * (∫ x, w x ∂π) - (2 * a) * (∫ x, w x * φ x ∂π) +
          (∫ x, w x * (φ x) ^ 2 ∂π)) =
        (∫ x, w x ∂π) * (∫ x, w x * (φ x) ^ 2 ∂π) -
          (∫ x, w x * φ x ∂π) ^ 2 := by
      dsimp [a]
      field_simp [ne_of_gt hApos]
      ring
    rw [hidentity] at hmul
    linarith

/-- The manuscript's nonnegative upper frame estimate for arbitrary finite
parameter and state measures. The coefficient is the actual squared integral
inner product, integrated over the parameter measure. All row and column
bounds are almost everywhere, and product integrability is derived rather
than assumed. The first conclusion records genuine coefficient integrability.

The column integrability hypothesis expresses that its finite real integral
is an actual finite integral; the final spectral theorem derives this from
the corresponding bounded nonnegative Lebesgue integral. -/
theorem measure_nonnegative_frame_bound {U X : Type*}
    [MeasurableSpace U] [MeasurableSpace X]
    (μ : Measure U) (π : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (f : U → X → ℝ) (φ : X → ℝ) (R C : ℝ)
    (hf : Measurable (Function.uncurry f)) (hφ : Measurable φ)
    (hfnonneg : ∀ u x, 0 ≤ f u x) (hR : 0 ≤ R)
    (hrowInt : ∀ᵐ u ∂μ, Integrable (f u) π)
    (hrow : ∀ᵐ u ∂μ, (∫ x, f u x ∂π) ≤ R)
    (hcolInt : ∀ᵐ x ∂π, Integrable (fun u => f u x) μ)
    (hcol : ∀ᵐ x ∂π, (∫ u, f u x ∂μ) ≤ C)
    (hφsquare : Integrable (fun x => (φ x) ^ 2) π)
    (hφnorm : (∫ x, (φ x) ^ 2 ∂π) = 1) :
    Integrable (fun u => (∫ x, f u x * φ x ∂π) ^ 2) μ ∧
      (∫ u, (∫ x, f u x * φ x ∂π) ^ 2 ∂μ) ≤ R * C := by
  let g : U × X → ℝ := fun z => f z.1 z.2 * (φ z.2) ^ 2
  have hgmeas : Measurable g := hf.mul ((hφ.comp measurable_snd).pow_const 2)
  have hgnonneg : ∀ z, 0 ≤ g z :=
    fun z => mul_nonneg (hfnonneg z.1 z.2) (sq_nonneg _)
  have hnormcolumn : (fun x => ∫ u, ‖g (u, x)‖ ∂μ) =
      (fun x => (∫ u, f u x ∂μ) * (φ x) ^ 2) := by
    funext x
    simp only [g, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfnonneg _ _) (sq_nonneg _)),
      integral_mul_const]
  have hcolumnmeas : AEStronglyMeasurable (fun x => ∫ u, ‖g (u, x)‖ ∂μ) π :=
    hgmeas.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  have hnormcolumnInt : Integrable (fun x => ∫ u, ‖g (u, x)‖ ∂μ) π := by
    apply (hφsquare.const_mul C).mono' hcolumnmeas
    filter_upwards [hcol] with x hx
    have hnon : 0 ≤ ∫ u, f u x ∂μ := integral_nonneg (hfnonneg · x)
    rw [congrFun hnormcolumn x]
    change ‖(∫ u, f u x ∂μ) * (φ x) ^ 2‖ ≤ C * (φ x) ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg hnon (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  have hgInt : Integrable g (μ.prod π) := by
    apply (integrable_prod_iff' hgmeas.aestronglyMeasurable).2
    refine ⟨?_, hnormcolumnInt⟩
    filter_upwards [hcolInt] with x hx
    exact hx.mul_const ((φ x) ^ 2)
  have hrowSquareInt : ∀ᵐ u ∂μ, Integrable (fun x => f u x * (φ x) ^ 2) π :=
    hgInt.prod_right_ae
  have hweightBound : ∀ᵐ u ∂μ,
      (∫ x, f u x * φ x ∂π) ^ 2 ≤ R * (∫ x, f u x * (φ x) ^ 2 ∂π) := by
    filter_upwards [hrowInt, hrow, hrowSquareInt] with u huInt hu huSquare
    have hcs := integral_weighted_cauchy π (f u) φ
      (Eventually.of_forall (hfnonneg u)) huInt hφ.aestronglyMeasurable huSquare
    have hnormnonneg : 0 ≤ ∫ x, f u x * (φ x) ^ 2 ∂π :=
      integral_nonneg (fun x => mul_nonneg (hfnonneg u x) (sq_nonneg _))
    exact hcs.trans (mul_le_mul_of_nonneg_right hu hnormnonneg)
  have hcoefmeas : AEStronglyMeasurable
      (fun u => (∫ x, f u x * φ x ∂π) ^ 2) μ :=
    ((hf.mul (hφ.comp measurable_snd)).stronglyMeasurable.integral_prod_right').pow 2
      |>.aestronglyMeasurable
  have hdomInt : Integrable (fun u => R * (∫ x, f u x * (φ x) ^ 2 ∂π)) μ :=
    hgInt.integral_prod_left.const_mul R
  have hcoefInt : Integrable (fun u => (∫ x, f u x * φ x ∂π) ^ 2) μ :=
    hdomInt.mono_nonneg hcoefmeas (Eventually.of_forall (fun _ => sq_nonneg _)) hweightBound
  refine ⟨hcoefInt, ?_⟩
  have hsecond : (∫ x, ∫ u, f u x * (φ x) ^ 2 ∂μ ∂π) ≤ C := by
    calc
      _ ≤ ∫ x, C * (φ x) ^ 2 ∂π := by
        apply integral_mono_ae hgInt.integral_prod_right (hφsquare.const_mul C)
        filter_upwards [hcol] with x hx
        change (∫ u, f u x * (φ x) ^ 2 ∂μ) ≤ C * (φ x) ^ 2
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
      _ = C := by rw [integral_const_mul, hφnorm, mul_one]
  calc
    _ ≤ ∫ u, R * (∫ x, f u x * (φ x) ^ 2 ∂π) ∂μ :=
      integral_mono_ae hcoefInt hdomInt hweightBound
    _ = R * (∫ u, ∫ x, f u x * (φ x) ^ 2 ∂π ∂μ) := integral_const_mul _ _
    _ = R * (∫ x, ∫ u, f u x * (φ x) ^ 2 ∂μ ∂π) := by
      rw [integral_integral_swap hgInt]
    _ ≤ R * C := mul_le_mul_of_nonneg_left hsecond hR

/-- Full parameter-measure counting argument of manuscript `lem:sp-frame`
for an actual real `L²(π)` Hilbert basis and its spectral quadratic form.

The trial functions and eigenfunctions are genuine measurable representatives
of `L²` elements. Nonnegativity, the almost-everywhere row bound, and the
almost-everywhere nonnegative Lebesgue column bound imply the upper frame
estimate by weighted Cauchy--Schwarz and Fubini. Hilbert-basis Parseval and
nonnegative series integration then derive, rather than assume, the trace
and energy identities for the integrated spectral coefficients.

`hform` is actual membership in the spectral quadratic-form domain;
`spectralFrameEnergy` is the corresponding convergent weighted basis series.
Identifying this form and basis with the spherical Langevin generator remains
a spectral-realization obligation. No coefficient-frame bound or integrated
coefficient mass/energy identity is supplied as a hypothesis.

The finite set `s` contains exactly the eigenvalues below the cutoff,
including a zero eigenvalue when present. Finiteness of that cutoff spectrum
is explicit; the result also holds with zero total trace. -/
theorem measure_frame_spectral_count {U X : Type*}
    [MeasurableSpace U] [MeasurableSpace X]
    (μ : Measure U) (π : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure π]
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 π)) (F : U → Lp ℝ 2 π)
    (f : U → X → ℝ) (φ : ℕ → X → ℝ) (eigenvalue : ℕ → ℝ)
    (s : Finset ℕ) (r Λ R C : ℝ)
    (hf : Measurable (Function.uncurry f)) (hfnonneg : ∀ u x, 0 ≤ f u x)
    (hFrep : ∀ u, f u =ᵐ[π] F u)
    (hφmeas : ∀ j, Measurable (φ j)) (hφrep : ∀ j, φ j =ᵐ[π] basis j)
    (hR : 0 < R) (hC : 0 < C) (hr : 0 ≤ r) (hrΛ : r < Λ)
    (hrow : ∀ᵐ u ∂μ, (∫ x, f u x ∂π) ≤ R)
    (hcol : ∀ᵐ x ∂π,
      (∫⁻ u, ENNReal.ofReal (f u x) ∂μ) ≤ ENNReal.ofReal C)
    (hmass : Integrable (fun u => ‖F u‖ ^ 2) μ)
    (hEigenvalue : ∀ j, 0 ≤ eigenvalue j)
    (hcut : ∀ j, j ∈ s ↔ eigenvalue j ≤ Λ)
    (hform : ∀ᵐ u ∂μ,
      Summable (fun j => eigenvalue j * (inner ℝ (basis j) (F u)) ^ 2))
    (henergyInt : Integrable (spectralFrameEnergy basis eigenvalue F) μ)
    (henergy : (∫ u, spectralFrameEnergy basis eigenvalue F u ∂μ) ≤
      r * (∫ u, ‖F u‖ ^ 2 ∂μ)) :
    (1 - r / Λ) * (∫ u, ‖F u‖ ^ 2 ∂μ) / (R * C) ≤ (s.card : ℝ) := by
  let b : ℕ → ℝ := fun j => ∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ
  have hcoefeq : ∀ j u, inner ℝ (basis j) (F u) = ∫ x, f u x * φ j x ∂π :=
    L2_basis_coefficient_eq_integral π basis F f φ hFrep hφrep
  have hcoefmeas : ∀ j, AEStronglyMeasurable (fun u => inner ℝ (basis j) (F u)) μ := by
    intro j
    have heq : (fun u => inner ℝ (basis j) (F u)) =
        (fun u => ∫ x, f u x * φ j x ∂π) := funext (hcoefeq j)
    rw [heq]
    exact (hf.mul ((hφmeas j).comp measurable_snd)).stronglyMeasurable.integral_prod_right'
      |>.aestronglyMeasurable
  have hrowInt : ∀ᵐ u ∂μ, Integrable (f u) π := Eventually.of_forall (fun u =>
    (MemLp.integrable (by norm_num) (Lp.memLp (F u))).congr (hFrep u).symm)
  have hcolumns := frame_column_integrable_of_lintegral_bound (μ := μ)
    π f C hf hfnonneg hC.le hcol
  have hb : ∀ j, 0 ≤ b j := fun j => integral_nonneg (fun _ => sq_nonneg _)
  have hbBound : ∀ j, b j ≤ R * C := by
    intro j
    obtain ⟨hφsquare, hφnorm⟩ :=
      L2_basis_representative_integrable_sq_and_normalized π basis φ hφrep j
    have hframe := measure_nonnegative_frame_bound μ π f (φ j) R C hf (hφmeas j)
      hfnonneg hR.le hrowInt hrow (hcolumns.mono fun _ h => h.1)
      (hcolumns.mono fun _ h => h.2) hφsquare hφnorm
    dsimp [b]
    simp_rw [hcoefeq j]
    exact hframe.2
  have hmassSum := integrated_L2_parseval (μ := μ) π basis F hcoefmeas hmass
  have henergySum := integrated_spectral_energy (μ := μ) basis eigenvalue F
    hcoefmeas hEigenvalue hform henergyInt
  have henergyb : (∑' j, eigenvalue j * b j) ≤ r * (∑' j, b j) := by
    change (∑' j, eigenvalue j * (∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ)) ≤
      r * (∑' j, (∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ))
    rw [henergySum.tsum_eq, hmassSum.tsum_eq]
    exact henergy
  have hcount := summable_weighted_spectral_count s eigenvalue b r Λ (R * C)
    hcut hb hEigenvalue hbBound (mul_pos hR hC) hr hrΛ
    hmassSum.summable henergySum.summable henergyb
  simpa only [b, hmassSum.tsum_eq] using hcount

end SlowEquilibration
