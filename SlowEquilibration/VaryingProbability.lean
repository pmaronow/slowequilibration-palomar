-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.Separation

/-! Convergence in probability when the genuine disorder spaces and their
probability laws vary with dimension. The source capture window is selected
before taking the dimension limit. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.VaryingProbability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]

/-- The ordinary probability-limit definition on actual varying spaces. -/
def InProbability (d : ∀ N, Measure (Ω N)) (f : ∀ N, Ω N → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => (d N).real {ω | ε ≤ ‖f N ω - c‖}) atTop (𝓝 0)

/-- Expected nonnegative error tending to zero implies the genuine
dimension-dependent convergence in probability, by Markov. -/
theorem inProbability_zero_of_integral_tendsto_zero
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (f : ∀ N, Ω N → ℝ) (hf : ∀ N ω, 0 ≤ f N ω)
    (hint : ∀ N, Integrable (f N) (d N))
    (hmean : Tendsto (fun N => ∫ ω, f N ω ∂d N) atTop (𝓝 0)) : InProbability d f 0 := by
  intro ε hε
  have hbound (N : ℕ) : (d N).real {ω | ε ≤ ‖f N ω - 0‖} ≤
      (∫ ω, f N ω ∂d N) / ε := by
    have hmark := mul_meas_ge_le_integral_of_nonneg (μ := d N)
      (.of_forall (hf N)) (hint N) ε
    have he : {ω | ε ≤ ‖f N ω - 0‖} = {ω | ε ≤ f N ω} := by
      ext ω
      change (ε ≤ ‖f N ω - 0‖) ↔ ε ≤ f N ω
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg (hf N ω)]
    rw [he]
    apply (le_div_iff₀ hε).mpr
    nlinarith
  exact squeeze_zero (fun N => measureReal_nonneg) hbound (by simpa using hmean.div_const ε)

/-- Literal varying-space version of source `lem:red-test`. Capture is
the original two-scale expected complement-mass premise. -/
theorem testing_band_union (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (Δ : ∀ N, Ω N → ℝ) (C E : ∀ N, ℝ → Ω N → ℝ)
    (hΔ : ∀ N ω, Δ N ω ≤ 1)
    (hC : ∀ N M, 0 < M → ∀ ω, 0 ≤ C N M ω)
    (hE : ∀ N M, 0 < M → ∀ ω, 0 ≤ E N M ω)
    (hCint : ∀ N M, 0 < M → Integrable (C N M) (d N))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, C N M ω ∂d N) < η)
    (herror : ∀ M : ℝ, 0 < M → InProbability d (fun N => E N M) 0)
    (hbound : ∀ N M, 0 < M → ∀ ω, 1-C N M ω-E N M ω ≤ Δ N ω) :
    InProbability d Δ 1 := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall (fun N => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    obtain ⟨M,hM,hcap⟩ := hcapture (ε*δ/4) (by positivity)
    have herr := herror M hM (ε/2) (by positivity)
    have herr' : ∀ᶠ N in atTop, (d N).real {ω | ε/2 ≤ ‖E N M ω - 0‖} < δ/2 :=
      (tendsto_order.mp herr).2 (δ/2) (by positivity)
    filter_upwards [hcap,herr'] with N hcapN herrN
    have hmark := mul_meas_ge_le_integral_of_nonneg (μ := d N)
      (.of_forall (hC N M hM)) (hCint N M hM) (ε/2)
    have hcapTail : (d N).real {ω | ε/2 ≤ C N M ω} < δ/2 := by nlinarith
    have hsub : {ω | ε ≤ ‖Δ N ω - 1‖} ⊆
        {ω | ε/2 ≤ C N M ω} ∪ {ω | ε/2 ≤ ‖E N M ω - 0‖} := by
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at *
      have hnorm : ‖Δ N ω - 1‖ = 1-Δ N ω := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hΔ N ω])]
        ring
      have hEnorm : ‖E N M ω - 0‖ = E N M ω := by
        simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (hE N M hM ω)]
      rw [hnorm] at hω
      rw [hEnorm]
      by_contra h
      push Not at h
      linarith [hbound N M hM ω]
    have hp := (measureReal_mono (μ := d N) hsub).trans (measureReal_union_le (μ := d N) _ _)
    linarith

end SlowEquilibration.VaryingProbability
