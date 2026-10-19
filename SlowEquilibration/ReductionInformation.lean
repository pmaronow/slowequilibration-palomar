-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntropyTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual probability-measure information transfer with the source
polynomial reference-event bound. The measurable spaces may vary with N.
The small-information premise is actual KL = o(log N), expressed with
extended-real inequalities so infinity is not silently mapped to zero. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.ReductionInformation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The nonnegative extended-real meaning of o(log N). In particular it
implies finiteness for all sufficiently large N. -/
def LittleLog (I : ℕ → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, I N ≤ ENNReal.ofReal (ε * Real.log N)

variable {α : Type*} [MeasurableSpace α]

/-- Exact polynomial-event denominator in the finite-volume binary test,
including the zero-reference-mass boundary case. -/
theorem polynomial_event_entropy_bound (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ν ≠ ∞) {B : Set α} (hB : MeasurableSet B)
    {N : ℕ} (hN : 0 < N) {C ζ : ℝ} (hC : 0 < C)
    (hpoly : ν.real B ≤ C * (N : ℝ) ^ (-ζ))
    (hden : 0 < ζ * Real.log N - Real.log C) :
    μ.real B ≤ ((InformationTheory.klDiv μ ν).toReal + Real.log 2) /
      (ζ * Real.log N - Real.log C) := by
  have hnum : 0 ≤ (InformationTheory.klDiv μ ν).toReal + Real.log 2 :=
    add_nonneg ENNReal.toReal_nonneg (Real.log_nonneg (by norm_num))
  by_cases hz : ν.real B = 0
  · have hνB : ν B = 0 := (measureReal_eq_zero_iff (μ := ν) (s := B)).mp hz
    have hμB := (InformationTheory.klDiv_ne_top_iff.mp hKL).1 hνB
    simp only [Measure.real, hμB, ENNReal.toReal_zero]
    exact div_nonneg hnum hden.le
  have ha0 : 0 < ν.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlog := Real.log_le_log ha0 hpoly
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hNreal (-ζ)).ne', Real.log_rpow hNreal] at hlog
  have hlower : ζ * Real.log N - Real.log C ≤ Real.log (1 / ν.real B) := by
    rw [one_div, Real.log_inv]
    linarith
  have ha1 : ν.real B < 1 := by
    apply lt_of_le_of_ne measureReal_le_one
    intro hone
    rw [hone] at hlower
    norm_num at hlower
    linarith
  have hb := relativeEntropy_event_probability_bound μ ν hKL hB ha0 ha1
  exact hb.trans (div_le_div_of_nonneg_left hnum hden hlower)

variable {A E : ℕ → Type*} [∀ N, MeasurableSpace (A N)] [∀ N, MeasurableSpace (E N)]

/-- Information data processing on actual varying probability spaces:
polynomially rare reference events remain rare after a field-dependent
initial law carrying o(log N) information. The transition is a genuine
Markov kernel, and the information is the actual initial KL. -/
theorem event_mass_tendsto_zero_of_littleLog
    (μ ν : ∀ N, Measure (A N)) [∀ N, IsProbabilityMeasure (μ N)] [∀ N, IsProbabilityMeasure (ν N)]
    (K : ∀ N, Kernel (A N) (E N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, Set (E N)) (hB : ∀ N, MeasurableSet (B N))
    {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ)
    (hpoly : ∀ᶠ N : ℕ in atTop, ((K N) ∘ₘ (ν N)).real (B N) ≤ C * (N : ℝ)^(-ζ))
    (hI : LittleLog (fun N => InformationTheory.klDiv (μ N) (ν N))) :
    Tendsto (fun N => ((K N) ∘ₘ (μ N)).real (B N)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall (fun N => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    let ε := δ * ζ / 8
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hlarge := hlog.eventually (eventually_gt_atTop
      (max (2 * Real.log C / ζ) (Real.log 2 / ε)))
    filter_upwards [hpoly, hI ε hε, hlarge, eventually_ge_atTop 2] with N hpolyN hIN hlargeN hN
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hCsmall : Real.log C < ζ * Real.log N / 2 := by
      have hh := lt_of_le_of_lt (le_max_left _ _) hlargeN
      have hd := (div_lt_iff₀ hζ).mp hh
      linarith
    have h2small : Real.log 2 < ε * Real.log N := by
      have hh := lt_of_le_of_lt (le_max_right _ _) hlargeN
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hh
    have hden : 0 < ζ * Real.log N - Real.log C := by nlinarith
    have hKL : InformationTheory.klDiv (μ N) (ν N) ≠ ∞ :=
      ne_of_lt (hIN.trans_lt ENNReal.ofReal_lt_top)
    have hcon := relativeEntropy_kernel_contraction (μ N) (ν N) (K N)
    have hKLout : InformationTheory.klDiv ((K N) ∘ₘ (μ N)) ((K N) ∘ₘ (ν N)) ≠ ∞ :=
      ne_of_lt (hcon.trans_lt (lt_top_iff_ne_top.mpr hKL))
    have hb := polynomial_event_entropy_bound ((K N) ∘ₘ (μ N)) ((K N) ∘ₘ (ν N))
      hKLout (hB N) (show 0 < N by omega) hC hpolyN hden
    have hiReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIN
    rw [ENNReal.toReal_ofReal (mul_nonneg hε.le hL.le)] at hiReal
    have hoReal := ENNReal.toReal_mono hKL hcon
    have hmass := (le_div_iff₀ hden).mp hb
    have hp := measureReal_nonneg (μ := (K N) ∘ₘ (μ N)) (s := B N)
    have hεeq : 8 * ε = δ * ζ := by dsimp [ε]; ring
    nlinarith

end SlowEquilibration.ReductionInformation
