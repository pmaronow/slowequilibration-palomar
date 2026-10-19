-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNormConcentration
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Passage of genuine finite Gaussian deviation bounds to their almost-sure
limits. Strict upper tails require no atom hypothesis at the limiting threshold. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianConcentrationLimit
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A uniform finite-approximation bound passes to the literal strict tail of
an almost-sure limit, by continuity from below of the eventual event. -/
theorem strict_tail_bound_of_ae_tendsto (X : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hX : ∀ n,Measurable (X n))
    (hlim : ∀ᵐ ω ∂μ,Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (a : ℝ) (C : ℝ≥0∞) (hbound : ∀ n,μ {ω|a<X n ω}≤C) :
    μ {ω|a<Z ω}≤C := by
  let E : ℕ → Set Ω := fun m => ⋂ n≥m,{ω|a<X n ω}
  have hE : ∀ m,MeasurableSet (E m) := fun m => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => measurableSet_lt measurable_const (hX n)
  have hmono : Monotone E := by
    intro m k hmk ω hω
    simp only [E,mem_iInter] at hω ⊢
    exact fun n hkn => hω n (hmk.trans hkn)
  have hsub : {ω|a<Z ω}≤ᵐ[μ] ⋃ m,E m := by
    filter_upwards [hlim] with ω hω
    intro ha
    have ht := hω.eventually (Ioi_mem_nhds ha)
    obtain ⟨m,hm⟩ := eventually_atTop.mp ht
    exact mem_iUnion.mpr ⟨m,by simpa only [E,mem_iInter,mem_setOf_eq] using hm⟩
  calc
    μ {ω|a<Z ω} ≤ μ (⋃ m,E m) := measure_mono_ae hsub
    _ = ⨆ m,μ (E m) := hmono.measure_iUnion
    _ ≤ C := iSup_le fun m => (measure_mono (by
      intro ω hω
      exact (mem_iInter.mp (mem_iInter.mp hω m) le_rfl))).trans (hbound m)

/-- Actual centered deviations pass through simultaneous almost-sure and mean
convergence. The finite concentration estimates remain the sole probabilistic input. -/
theorem centered_strict_tail_of_ae_tendsto [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (Z : Ω → ℝ) (hX : ∀ n,Measurable (X n))
    (hlim : ∀ᵐ ω ∂μ,Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (hmean : Tendsto (fun n => ∫ ω,X n ω ∂μ) atTop (𝓝 (∫ ω,Z ω ∂μ)))
    {L s : ℝ} (hbound : ∀ n,μ {ω|s<X n ω-(∫ ω,X n ω ∂μ)}≤
      ENNReal.ofReal (Real.exp (-s^2/(2*L^2)))) :
    μ {ω|(∫ ω,Z ω ∂μ)+s<Z ω}≤ENNReal.ofReal (Real.exp (-s^2/(2*L^2))) := by
  have h := strict_tail_bound_of_ae_tendsto
    (fun n ω => X n ω-(∫ ω,X n ω ∂μ)) (fun ω => Z ω-(∫ ω,Z ω ∂μ))
    (fun n => (hX n).sub measurable_const)
    (hlim.mono fun ω hω => hω.sub hmean) s _ hbound
  have he : {ω|(∫ ω,Z ω ∂μ)+s<Z ω}={ω|s<Z ω-(∫ ω,Z ω ∂μ)} := by
    ext ω
    simp only [mem_setOf_eq]
    constructor <;> intro hh <;> linarith
  rw [he]
  exact h

end SlowEquilibration.GaussianConcentrationLimit
