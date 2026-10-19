-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Integrated spectral mass and energy

This file proves the Parseval and Tonelli steps in manuscript Lemma
`lem:sp-frame`.  The coefficients are actual inner products with a real
Hilbert basis.  The `L²` specialization uses Mathlib's `Lp ℝ 2 π` space.
Integrated coefficient mass and weighted energy are derived, with convergence,
from coefficient measurability and finite mass or finite spectral form energy.

No construction of the spherical Langevin generator, its compact resolvent,
or its eigenbasis is claimed.  A supplied Hilbert basis and nonnegative
spectrum are genuine analytic inputs.
-/

namespace SlowEquilibration

open MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal

variable {U H : Type*} [MeasurableSpace U] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {μ : Measure U}

/-- Tonelli's series argument, in real-integral form.  Nonnegativity and pointwise
summability prevent the real-valued `tsum` convention from hiding divergence. -/
theorem integral_sum_nonnegative_series (a : ℕ → U → ℝ)
    (hmeas : ∀ j, AEStronglyMeasurable (a j) μ)
    (hnonneg : ∀ j u, 0 ≤ a j u)
    (hsum : ∀ᵐ u ∂μ, Summable (fun j => a j u))
    (hint : Integrable (fun u => ∑' j, a j u) μ) :
    HasSum (fun j => ∫ u, a j u ∂μ) (∫ u, ∑' j, a j u ∂μ) := by
  apply hasSum_integral_of_dominated_convergence a hmeas
  · intro j
    exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg j u)])
  · exact hsum
  · exact hint
  · exact hsum.mono fun _ h => h.hasSum

/-- Finite extended nonnegative energy implies convergence and integrability of
its real series.  This is the useful Tonelli hypothesis when no separate
quadratic-form-domain assumption is available. -/
theorem nonnegative_series_of_finite_lintegral (a : ℕ → U → ℝ)
    (hmeas : ∀ j, AEStronglyMeasurable (a j) μ)
    (hnonneg : ∀ j u, 0 ≤ a j u)
    (hfinite : (∫⁻ u, ∑' j, ENNReal.ofReal (a j u) ∂μ) ≠ ∞) :
    (∀ᵐ u ∂μ, Summable (fun j => a j u)) ∧
      Integrable (fun u => ∑' j, a j u) μ := by
  have hEmeas : AEMeasurable (fun u => ∑' j, ENNReal.ofReal (a j u)) μ :=
    AEMeasurable.tsum (fun j => (hmeas j).aemeasurable.ennreal_ofReal)
  have hid : (fun u => (∑' j, ENNReal.ofReal (a j u)).toReal) =
      (fun u => ∑' j, a j u) := by
    ext u
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hnonneg _ _)]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_lt_top' hEmeas hfinite] with u hu
    have ht := ENNReal.summable_toReal hu.ne
    simpa only [ENNReal.toReal_ofReal (hnonneg _ _)] using ht
  · rw [← hid]
    exact ⟨hEmeas.ennreal_toReal.aestronglyMeasurable,
      hasFiniteIntegral_toReal_of_lintegral_ne_top hfinite⟩

/-- Tonelli for nonnegative real series with finite extended total integral.
Neither convergence nor the integrated series identity is assumed. -/
theorem integral_sum_nonnegative_series_of_finite_lintegral (a : ℕ → U → ℝ)
    (hmeas : ∀ j, AEStronglyMeasurable (a j) μ)
    (hnonneg : ∀ j u, 0 ≤ a j u)
    (hfinite : (∫⁻ u, ∑' j, ENNReal.ofReal (a j u) ∂μ) ≠ ∞) :
    HasSum (fun j => ∫ u, a j u ∂μ) (∫ u, ∑' j, a j u ∂μ) := by
  obtain ⟨hsum, hint⟩ := nonnegative_series_of_finite_lintegral a hmeas hnonneg hfinite
  exact integral_sum_nonnegative_series a hmeas hnonneg hsum hint

/-- Parseval for an actual real Hilbert basis, including convergence. -/
theorem hilbert_parseval_hasSum (basis : HilbertBasis ℕ ℝ H) (v : H) :
    HasSum (fun j => (inner ℝ (basis j) v) ^ 2) (‖v‖ ^ 2) := by
  convert basis.hasSum_inner_mul_inner v v using 1
  · ext j
    rw [real_inner_comm v (basis j), pow_two]
  · exact (real_inner_self_eq_norm_sq v).symm

/-- Parseval followed by nonnegative series integration.  The coefficient
integrals are computed from the specified basis and family, not supplied as an
abstract spectral mass identity. -/
theorem integrated_hilbert_parseval (basis : HilbertBasis ℕ ℝ H) (F : U → H)
    (hcoef : ∀ j, AEStronglyMeasurable (fun u => inner ℝ (basis j) (F u)) μ)
    (hmass : Integrable (fun u => ‖F u‖ ^ 2) μ) :
    HasSum (fun j => ∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ)
      (∫ u, ‖F u‖ ^ 2 ∂μ) := by
  have hpoint : ∀ u, HasSum (fun j => (inner ℝ (basis j) (F u)) ^ 2) (‖F u‖ ^ 2) :=
    fun u => hilbert_parseval_hasSum basis (F u)
  have hid : (fun u => ∑' j, (inner ℝ (basis j) (F u)) ^ 2) =
      (fun u => ‖F u‖ ^ 2) := funext fun u => (hpoint u).tsum_eq
  have ht := integral_sum_nonnegative_series
    (fun j u => (inner ℝ (basis j) (F u)) ^ 2)
    (fun j => (hcoef j).pow 2) (fun _ _ => sq_nonneg _)
    (Filter.Eventually.of_forall (fun u => (hpoint u).summable)) (hid ▸ hmass)
  simpa only [hid] using ht

/-- Specialization of integrated Parseval to genuine `L²(π)` trial functions. -/
theorem integrated_L2_parseval {X : Type*} [MeasurableSpace X] (π : Measure X)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 π)) (F : U → Lp ℝ 2 π)
    (hcoef : ∀ j, AEStronglyMeasurable (fun u => inner ℝ (basis j) (F u)) μ)
    (hmass : Integrable (fun u => ‖F u‖ ^ 2) μ) :
    HasSum (fun j => ∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ)
      (∫ u, ‖F u‖ ^ 2 ∂μ) :=
  integrated_hilbert_parseval basis F hcoef hmass

/-- The spectral Dirichlet form of a family is the actual weighted coefficient
series.  Pointwise summability expresses membership in its quadratic-form domain. -/
noncomputable def spectralFrameEnergy (basis : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (F : U → H) (u : U) : ℝ :=
  ∑' j, eigenvalue j * (inner ℝ (basis j) (F u)) ^ 2

/-- Integrated spectral energy, with the genuine form-domain and integrability
hypotheses.  No equality between total energy and integrated coefficient energy
is assumed. -/
theorem integrated_spectral_energy (basis : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (F : U → H)
    (hcoef : ∀ j, AEStronglyMeasurable (fun u => inner ℝ (basis j) (F u)) μ)
    (heigenvalue : ∀ j, 0 ≤ eigenvalue j)
    (hform : ∀ᵐ u ∂μ,
      Summable (fun j => eigenvalue j * (inner ℝ (basis j) (F u)) ^ 2))
    (henergy : Integrable (spectralFrameEnergy basis eigenvalue F) μ) :
    HasSum (fun j => eigenvalue j * (∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ))
      (∫ u, spectralFrameEnergy basis eigenvalue F u ∂μ) := by
  have ht := integral_sum_nonnegative_series
    (fun j u => eigenvalue j * (inner ℝ (basis j) (F u)) ^ 2)
    (fun j => ((hcoef j).pow 2).const_mul (eigenvalue j))
    (fun j u => mul_nonneg (heigenvalue j) (sq_nonneg _)) hform henergy
  simpa only [spectralFrameEnergy, integral_const_mul] using ht

/-- Integrated spectral energy from finite extended energy alone.  Nonnegative
series convergence and real-energy integrability are derived by Tonelli. -/
theorem integrated_spectral_energy_of_finite_lintegral
    (basis : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ) (F : U → H)
    (hcoef : ∀ j, AEStronglyMeasurable (fun u => inner ℝ (basis j) (F u)) μ)
    (heigenvalue : ∀ j, 0 ≤ eigenvalue j)
    (hfinite : (∫⁻ u, ∑' j, ENNReal.ofReal
      (eigenvalue j * (inner ℝ (basis j) (F u)) ^ 2) ∂μ) ≠ ∞) :
    HasSum (fun j => eigenvalue j * (∫ u, (inner ℝ (basis j) (F u)) ^ 2 ∂μ))
      (∫ u, spectralFrameEnergy basis eigenvalue F u ∂μ) := by
  have ht := integral_sum_nonnegative_series_of_finite_lintegral
    (fun j u => eigenvalue j * (inner ℝ (basis j) (F u)) ^ 2)
    (fun j => ((hcoef j).pow 2).const_mul (eigenvalue j))
    (fun j u => mul_nonneg (heigenvalue j) (sq_nonneg _)) hfinite
  simpa only [spectralFrameEnergy, integral_const_mul] using ht

/-- An extended-integral bound for a nonnegative measurable function supplies
both real integrability and the corresponding real-integral bound. -/
theorem integrable_integral_le_of_nonnegative_lintegral_bound
    {X : Type*} [MeasurableSpace X] (π : Measure X) (f : X → ℝ) (C : ℝ)
    (hfmeas : AEStronglyMeasurable f π) (hfnonneg : ∀ᵐ x ∂π, 0 ≤ f x)
    (hC : 0 ≤ C) (hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂π) ≤ ENNReal.ofReal C) :
    Integrable f π ∧ (∫ x, f x ∂π) ≤ C := by
  have hfinite : (∫⁻ x, ENNReal.ofReal (f x) ∂π) < ∞ :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hint : Integrable f π :=
    ⟨hfmeas, (hasFiniteIntegral_iff_ofReal hfnonneg).2 hfinite⟩
  refine ⟨hint, (ENNReal.ofReal_le_ofReal_iff hC).1 ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hint hfnonneg]
  exact hbound

/-- For an actual jointly measurable nonnegative trial family, an extended
column bound implies integrable columns and the real column bound almost
 everywhere.  The statement works for arbitrary measures. -/
theorem frame_column_integrable_of_lintegral_bound
    {X : Type*} [MeasurableSpace X] (π : Measure X) (f : U → X → ℝ) (C : ℝ)
    (hfmeas : Measurable (Function.uncurry f)) (hfnonneg : ∀ u x, 0 ≤ f u x)
    (hC : 0 ≤ C)
    (hcolumn : ∀ᵐ x ∂π, (∫⁻ u, ENNReal.ofReal (f u x) ∂μ) ≤ ENNReal.ofReal C) :
    ∀ᵐ x ∂π, Integrable (fun u => f u x) μ ∧ (∫ u, f u x ∂μ) ≤ C := by
  filter_upwards [hcolumn] with x hx
  exact integrable_integral_le_of_nonnegative_lintegral_bound μ (fun u => f u x) C
    hfmeas.of_uncurry_right.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => hfnonneg u x)) hC hx

/-- The real `L²` inner product equals the integral of any supplied almost
 everywhere representatives.  No integral representation is assumed. -/
theorem L2_inner_eq_integral_representatives
    {X : Type*} [MeasurableSpace X] (π : Measure X) (v w : Lp ℝ 2 π)
    (f φ : X → ℝ) (hf : f =ᵐ[π] v) (hφ : φ =ᵐ[π] w) :
    inner ℝ w v = ∫ x, f x * φ x ∂π := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hφ] with x hx hy
  simp [← hx, ← hy]

/-- A chosen representative of an `L²` vector has integrable square and its
integral is the actual squared Hilbert norm. -/
theorem L2_representative_integrable_sq_and_norm
    {X : Type*} [MeasurableSpace X] (π : Measure X) (v : Lp ℝ 2 π)
    (f : X → ℝ) (hf : f =ᵐ[π] v) :
    Integrable (fun x => f x ^ 2) π ∧ ‖v‖ ^ 2 = ∫ x, f x ^ 2 ∂π := by
  refine ⟨((Lp.memLp v).ae_eq hf.symm).integrable_sq, ?_⟩
  have hinner := L2_inner_eq_integral_representatives π v v f f hf hf
  simpa only [pow_two] using (real_inner_self_eq_norm_sq v).symm.trans hinner

omit [MeasurableSpace U] in
/-- Actual Hilbert-basis coefficient formula for a chosen trial-function and
basis-function representative. -/
theorem L2_basis_coefficient_eq_integral
    {X : Type*} [MeasurableSpace X] (π : Measure X)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 π)) (F : U → Lp ℝ 2 π)
    (f : U → X → ℝ) (φ : ℕ → X → ℝ)
    (hf : ∀ u, f u =ᵐ[π] F u) (hφ : ∀ j, φ j =ᵐ[π] basis j) (j : ℕ) (u : U) :
    inner ℝ (basis j) (F u) = ∫ x, f u x * φ j x ∂π :=
  L2_inner_eq_integral_representatives π (F u) (basis j) (f u) (φ j) (hf u) (hφ j)

/-- A representative of a genuine unit Hilbert-basis vector has an integrable
square of integral one. -/
theorem L2_basis_representative_integrable_sq_and_normalized
    {X : Type*} [MeasurableSpace X] (π : Measure X)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 π)) (φ : ℕ → X → ℝ)
    (hφ : ∀ j, φ j =ᵐ[π] basis j) (j : ℕ) :
    Integrable (fun x => φ j x ^ 2) π ∧ (∫ x, φ j x ^ 2 ∂π) = 1 := by
  refine ⟨((Lp.memLp (basis j)).ae_eq (hφ j).symm).integrable_sq, ?_⟩
  have hinner := L2_inner_eq_integral_representatives π (basis j) (basis j)
    (φ j) (φ j) (hφ j) (hφ j)
  have hunit : inner ℝ (basis j) (basis j) = 1 := by
    simpa using orthonormal_iff_ite.mp basis.orthonormal j j
  simpa only [pow_two] using hinner.symm.trans hunit

end SlowEquilibration
