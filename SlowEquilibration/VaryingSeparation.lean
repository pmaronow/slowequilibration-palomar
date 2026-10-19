-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.Separation
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

namespace SlowEquilibration

open MeasureTheory Filter Set
open scoped Topology

/-- Convert the manuscript's iterated limsup capture statement into its
fixed-window eventual form. The upper bound justifies the real limsup. -/
theorem fixed_window_of_iterated_limsup (a : ℕ → ℝ → ℝ)
    (hbound : ∀ M,0<M → ∀ N,a N M≤1)
    (hlimit : Tendsto (fun M => limsup (fun N => a N M) atTop) atTop (𝓝 0)) :
    ∀ η : ℝ,0<η → ∃ M : ℝ,0<M ∧ ∀ᶠ N in atTop,a N M<η := by
  intro η hη
  have hsmall := (tendsto_order.mp hlimit).2 η hη
  have hpositive : ∀ᶠ M : ℝ in atTop,0<M := eventually_gt_atTop 0
  obtain ⟨M,hMsmall,hM⟩ := (hsmall.and hpositive).exists
  refine ⟨M,hM,eventually_lt_of_limsup_lt hMsmall ?_⟩
  exact isBoundedUnder_of ⟨1,hbound M hM⟩

/-- Ordinary convergence in probability for dimension-dependent sample
spaces and probability laws, stated through their actual tail probabilities. -/
def VaryingConvergesInProbability {Ω : ℕ → Type*}
    [∀ N,MeasurableSpace (Ω N)] (P : ∀ N,Measure (Ω N))
    (X Y : ∀ N,Ω N → ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → Tendsto (fun N => (P N).real {ω | ε≤‖X N ω-Y N ω‖}) atTop (𝓝 0)

/-- The band-union testing argument on the actual dimension-dependent
disorder laws; no common finite sample model is substituted. -/
theorem varying_testing_band_union {Ω : ℕ → Type*} [∀ N,MeasurableSpace (Ω N)]
    (P : ∀ N,Measure (Ω N)) [∀ N,IsProbabilityMeasure (P N)]
    (Δ : ∀ N,Ω N → ℝ) (C E : ∀ N,ℝ → Ω N → ℝ)
    (hΔ : ∀ N ω,Δ N ω≤1)
    (hC : ∀ N M,0<M → ∀ ω,0≤C N M ω)
    (hE : ∀ N M,0<M → ∀ ω,0≤E N M ω)
    (hCint : ∀ N M,0<M → Integrable (C N M) (P N))
    (hcapture : ∀ η : ℝ,0<η → ∃ M : ℝ,0<M ∧
      ∀ᶠ N in atTop,(∫ ω,C N M ω ∂P N)<η)
    (herror : ∀ M : ℝ,0<M → VaryingConvergesInProbability P
      (fun N => E N M) (fun _ _ => 0))
    (hbound : ∀ N M,0<M → ∀ ω,1-C N M ω-E N M ω≤Δ N ω) :
    VaryingConvergesInProbability P Δ (fun _ _ => 1) := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    obtain ⟨M,hM,hcap⟩ := hcapture (ε*δ/4) (by positivity)
    have herr := herror M hM (ε/2) (by positivity)
    have herr' : ∀ᶠ N in atTop,(P N).real {ω | ε/2≤‖E N M ω-0‖}<δ/2 :=
      (tendsto_order.mp herr).2 (δ/2) (by positivity)
    filter_upwards [hcap,herr'] with N hcapN herrN
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ:=P N) (Eventually.of_forall (hC N M hM)) (hCint N M hM) (ε/2)
    have hcaptail : (P N).real {ω | ε/2≤C N M ω}<δ/2 := by nlinarith
    have hsub : {ω : Ω N | ε≤‖Δ N ω-1‖} ⊆
        {ω | ε/2≤C N M ω} ∪ {ω | ε/2≤‖E N M ω-0‖} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq,Set.mem_union] at *
      have hnorm : ‖Δ N ω-1‖=1-Δ N ω := by
        rw [Real.norm_eq_abs,abs_of_nonpos (by linarith [hΔ N ω])]
        ring
      have hEnorm : ‖E N M ω-0‖=E N M ω := by
        simp [Real.norm_eq_abs,abs_of_nonneg (hE N M hM ω)]
      rw [hnorm] at hω
      rw [hEnorm]
      by_contra h
      push Not at h
      linarith [hbound N M hM ω]
    have hprob := (measureReal_mono (μ:=P N) hsub).trans
      (measureReal_union_le (μ:=P N) _ _)
    linarith

/-- Lemma red-test with the original iterated-limsup capture hypothesis,
on genuine dimension-dependent probability spaces. -/
theorem varying_testing_band_union_of_iterated_limsup
    {Ω : ℕ → Type*} [∀ N,MeasurableSpace (Ω N)]
    (P : ∀ N,Measure (Ω N)) [∀ N,IsProbabilityMeasure (P N)]
    (Δ : ∀ N,Ω N → ℝ) (C E : ∀ N,ℝ → Ω N → ℝ)
    (hΔ : ∀ N ω,Δ N ω≤1)
    (hC : ∀ N M,0<M → ∀ ω,0≤C N M ω)
    (hCupper : ∀ N M,0<M → ∀ ω,C N M ω≤1)
    (hE : ∀ N M,0<M → ∀ ω,0≤E N M ω)
    (hCint : ∀ N M,0<M → Integrable (C N M) (P N))
    (hcapture : Tendsto (fun M => limsup (fun N => ∫ ω,C N M ω ∂P N) atTop)
      atTop (𝓝 0))
    (herror : ∀ M : ℝ,0<M → VaryingConvergesInProbability P
      (fun N => E N M) (fun _ _ => 0))
    (hbound : ∀ N M,0<M → ∀ ω,1-C N M ω-E N M ω≤Δ N ω) :
    VaryingConvergesInProbability P Δ (fun _ _ => 1) := by
  apply varying_testing_band_union P Δ C E hΔ hC hE hCint _ herror hbound
  apply fixed_window_of_iterated_limsup _ _ hcapture
  intro M hM N
  have hi := integral_mono_ae (hCint N M hM) (integrable_const (1:ℝ))
    (Eventually.of_forall (hCupper N M hM))
  simpa using hi

end SlowEquilibration
