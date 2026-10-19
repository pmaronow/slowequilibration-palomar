-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionJointInformation
public import SlowEquilibration.VaryingProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The conditional-entropy core of source `cor:red-entropy`. The KL is
the genuine relative entropy of the field-dependent initial kernel against
the prescribed field-independent law. Infinite values are counted in the
bad-field events, rather than being erased by ENNReal.toReal. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.ReductionEntropy

open MeasureTheory ProbabilityTheory Set Filter
open ReductionInformation ReductionJointInformation VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Exact source finite-volume transfer on one field. -/
theorem conditional_polynomial_mass_bound (μ : Kernel Ω X) [IsMarkovKernel μ]
    (ν : Measure X) [IsProbabilityMeasure ν] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) (ω : Ω)
    (hKL : InformationTheory.klDiv (μ ω) ν ≠ ∞)
    {N : ℕ} (hN : 0 < N) {C τ : ℝ} (hC : 0 < C)
    (hpoly : conditionalMass (Kernel.const Ω ν) K B ω ≤ C*(N : ℝ)^(-τ))
    (hden : 0 < τ*Real.log N-Real.log C) :
    conditionalMass μ K B ω ≤ ((InformationTheory.klDiv (μ ω) ν).toReal + Real.log 2) /
      (τ*Real.log N-Real.log C) := by
  let L := conditionalKernel K ω
  have hcon := relativeEntropy_kernel_contraction (μ ω) ν L
  have hKLout : InformationTheory.klDiv (L ∘ₘ μ ω) (L ∘ₘ ν) ≠ ∞ :=
    ne_of_lt (hcon.trans_lt (lt_top_iff_ne_top.mpr hKL))
  have hpoly' : (L ∘ₘ ν).real (Prod.mk ω ⁻¹' B) ≤ C*(N : ℝ)^(-τ) := by
    change (conditionalKernel K ω ∘ₘ ν).real (Prod.mk ω ⁻¹' B) ≤ _
    simpa only [conditionalMass, evolvedKernel_apply, Kernel.const_apply] using hpoly
  have hb := polynomial_event_entropy_bound (L ∘ₘ μ ω) (L ∘ₘ ν)
    hKLout (measurable_prodMk_left hB) hN hC hpoly' hden
  have hreal := ENNReal.toReal_mono hKL hcon
  have hr : ((InformationTheory.klDiv (L ∘ₘ μ ω) (L ∘ₘ ν)).toReal + Real.log 2) /
      (τ*Real.log N-Real.log C) ≤ ((InformationTheory.klDiv (μ ω) ν).toReal + Real.log 2) /
      (τ*Real.log N-Real.log C) := by
    apply div_le_div_of_nonneg_right _ hden.le
    linarith
  have hm : conditionalMass μ K B ω = (L ∘ₘ μ ω).real (Prod.mk ω ⁻¹' B) := by
    rw [conditionalMass, evolvedKernel_apply]
  rw [hm]
  exact hb.trans hr

variable {D S : ℕ → Type*} [∀ N, MeasurableSpace (D N)] [∀ N, MeasurableSpace (S N)]

/-- Actual KL/log N tends to zero in probability, including the extended
value infinity. On N≥2 these are exactly its ordinary scaled tail events. -/
def LittleLogInProbability (d : ∀ N, Measure (D N)) (I : ∀ N, D N → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => (d N).real {ω | ENNReal.ofReal (ε*Real.log N) ≤ I N ω}) atTop (𝓝 0)

/-- The reference endpoint band mass exceeds N^(-τ) only with the source
polynomial Markov bound C N^(τ−ζ), for every fixed τ∈(0,ζ). -/
theorem reference_bad_mass_tendsto_zero
    (d : ∀ N, Measure (D N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, Measure (S N)) [∀ N, IsProbabilityMeasure (ν N)]
    (K : ∀ N, Kernel (D N × S N) (S N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, Set (D N × S N)) (hB : ∀ N, MeasurableSet (B N))
    {C ζ τ : ℝ} (hτζ : τ < ζ)
    (hpoly : ∀ᶠ N : ℕ in atTop,
      (∫ ω, conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω ∂d N) ≤ C*(N : ℝ)^(-ζ)) :
    Tendsto (fun N => (d N).real {ω | (N : ℝ)^(-τ) ≤
      conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω}) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => C*(N : ℝ)^(τ-ζ)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hτζ)).comp tendsto_natCast_atTop_atTop
    have he : -(ζ-τ) = τ-ζ := by ring_nf
    simpa only [Function.comp_apply, he, mul_zero] using ht.const_mul C
  have hbound : ∀ᶠ N : ℕ in atTop,
      (d N).real {ω | (N : ℝ)^(-τ) ≤ conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω} ≤
        C*(N : ℝ)^(τ-ζ) := by
    filter_upwards [hpoly, eventually_ge_atTop 1] with N hpolyN hN
    have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hthresh := Real.rpow_pos_of_pos hNreal (-τ)
    have hmark := mul_meas_ge_le_integral_of_nonneg (μ := d N)
      (.of_forall (fun ω => measureReal_nonneg))
      (conditionalMass_integrable (d N) (Kernel.const (D N) (ν N)) (K N) (hB N)) ((N : ℝ)^(-τ))
    change (N : ℝ)^(-τ) * (d N).real {ω | (N : ℝ)^(-τ) ≤
      conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω} ≤
      (∫ ω, conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω ∂d N) at hmark
    have hfirst : (d N).real {ω | (N : ℝ)^(-τ) ≤
        conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω} ≤
        (C*(N : ℝ)^(-ζ)) / (N : ℝ)^(-τ) := by
      apply (le_div_iff₀ hthresh).mpr
      nlinarith
    apply hfirst.trans_eq
    rw [mul_div_assoc, ← Real.rpow_sub hNreal]
    rw [show -ζ-(-τ) = τ-ζ by ring_nf]
  exact squeeze_zero' (.of_forall (fun N => measureReal_nonneg)) hbound hpow

/-- Actual field-dependent initial laws with KL/log N small only in
probability have vanishing endpoint band mass under the original
polynomial reference-average premise. -/
theorem conditional_mass_inProbability_of_entropy
    (d : ∀ N, Measure (D N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ : ∀ N, Kernel (D N) (S N)) [∀ N, IsMarkovKernel (μ N)]
    (ν : ∀ N, Measure (S N)) [∀ N, IsProbabilityMeasure (ν N)]
    (K : ∀ N, Kernel (D N × S N) (S N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, Set (D N × S N)) (hB : ∀ N, MeasurableSet (B N))
    {C ζ : ℝ} (hζ : 0 < ζ)
    (hpoly : ∀ᶠ N : ℕ in atTop,
      (∫ ω, conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω ∂d N) ≤ C*(N : ℝ)^(-ζ))
    (hI : LittleLogInProbability d (fun N ω => InformationTheory.klDiv (μ N ω) (ν N))) :
    InProbability d (fun N => conditionalMass (μ N) (K N) (B N)) 0 := by
  intro δ hδ
  let τ := ζ/2
  have hτ : 0 < τ := half_pos hζ
  have hτζ : τ < ζ := by dsimp [τ]; linarith
  let ε := δ*τ/8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbadRef := reference_bad_mass_tendsto_zero d ν K B hB hτζ hpoly
  have hbadI := hI ε hε
  have hsum := hbadRef.add hbadI
  simp only [add_zero] at hsum
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually (eventually_gt_atTop (Real.log 2/ε))
  have hbound : ∀ᶠ N : ℕ in atTop,
      (d N).real {ω | δ ≤ ‖conditionalMass (μ N) (K N) (B N) ω - 0‖} ≤
        (d N).real {ω | (N : ℝ)^(-τ) ≤ conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω} +
        (d N).real {ω | ENNReal.ofReal (ε*Real.log N) ≤ InformationTheory.klDiv (μ N ω) (ν N)} := by
    filter_upwards [hlarge, eventually_ge_atTop 2] with N hlargeN hN
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have h2small : Real.log 2 < ε*Real.log N := by
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlargeN
    have hsub : {ω | δ ≤ ‖conditionalMass (μ N) (K N) (B N) ω - 0‖} ⊆
        {ω | (N : ℝ)^(-τ) ≤ conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω} ∪
        {ω | ENNReal.ofReal (ε*Real.log N) ≤ InformationTheory.klDiv (μ N ω) (ν N)} := by
      intro ω hω
      by_contra hbad
      have ha : conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω < (N : ℝ)^(-τ) := by
        exact lt_of_not_ge (fun h => hbad (Or.inl h))
      have hIlt : InformationTheory.klDiv (μ N ω) (ν N) < ENNReal.ofReal (ε*Real.log N) :=
        lt_of_not_ge (fun h => hbad (Or.inr h))
      have hKL : InformationTheory.klDiv (μ N ω) (ν N) ≠ ∞ :=
        ne_of_lt (hIlt.trans ENNReal.ofReal_lt_top)
      have hp := conditional_polynomial_mass_bound (μ N) (ν N) (K N) (hB N) ω hKL
        (show 0 < N by omega) (show (0 : ℝ) < 1 by norm_num)
        (show conditionalMass (Kernel.const (D N) (ν N)) (K N) (B N) ω ≤ 1*(N : ℝ)^(-τ) by simpa using ha.le)
        (show 0 < τ*Real.log N-Real.log 1 by simp only [Real.log_one, sub_zero]; positivity)
      simp only [Real.log_one, sub_zero] at hp
      have hiReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIlt.le
      rw [ENNReal.toReal_ofReal (mul_nonneg hε.le hL.le)] at hiReal
      have hpMul := (le_div_iff₀ (mul_pos hτ hL)).mp hp
      have hnon : 0 ≤ conditionalMass (μ N) (K N) (B N) ω := measureReal_nonneg
      change δ ≤ ‖conditionalMass (μ N) (K N) (B N) ω - 0‖ at hω
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hnon] at hω
      have hεeq : 8*ε = δ*τ := by dsimp [ε]; ring_nf
      have hδMul := mul_le_mul_of_nonneg_right hω (mul_nonneg hτ.le hL.le)
      have heqL : δ*(τ*Real.log N) = 8*(ε*Real.log N) := by
        calc
          _ = (δ*τ)*Real.log N := by ring_nf
          _ = (8*ε)*Real.log N := by rw [← hεeq]
          _ = _ := by ring_nf
      rw [heqL] at hδMul
      nlinarith [mul_pos hε hL]
    exact (measureReal_mono (μ := d N) hsub).trans (measureReal_union_le (μ := d N) _ _)
  exact squeeze_zero' (.of_forall (fun N => measureReal_nonneg)) hbound hsum

end SlowEquilibration.ReductionEntropy
