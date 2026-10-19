-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGradientDefectIntegrable

/-! L¹ closure for the four terms of the source-pairing identity. The
gradient cross term is controlled by the same Fisher-defect and weighted
gradient-square densities as the energy argument. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_pair_integrable_of_energy
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (I κ k F U : E→ℝ) (a b : ι→E→ℝ)
    (hk : Measurable k) (hF : Measurable F) (hU : Measurable U)
    (ha : ∀ ij, Measurable (a ij)) (hb : ∀ ij, Measurable (b ij))
    (CI CF : ℝ) (hCI : 0≤CI) (hCF : 0≤CF)
    (hIb : ∀ᵐ z ∂ν,‖I z‖≤CI)
    (hFb : ∀ᵐ z ∂ν,1≤F z ∧ ‖F z‖≤CF)
    (hUb : ∀ᵐ z ∂ν,0≤U z ∧ U z≤1)
    (hIi : Integrable I ν) (hki : Integrable k ν)
    (hRi : Integrable (fun z => κ z*F z) ν)
    (hKi : Integrable (fun z => k z^2*
      (∑ ij, (a ij z)^2/F z)) ν)
    (hBi : Integrable (fun z => F z*
      (∑ ij, (b ij z)^2)) ν) :
    Integrable (fun z => I z*U z) ν ∧
    Integrable (fun z => κ z*F z*(1-U z)) ν ∧
    Integrable (fun z => k z*(I z-F z)*U z) ν ∧
    Integrable (fun z => k z*(∑ ij, a ij z*b ij z)) ν := by
  have hUn : ∀ᵐ z ∂ν,‖U z‖≤1 := hUb.mono (fun z hz => by
    rw [Real.norm_eq_abs,abs_of_nonneg hz.1]
    exact hz.2)
  have hOneUn : ∀ᵐ z ∂ν,‖1-U z‖≤1 := hUb.mono (fun z hz => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith)
  have hDiffUn : ∀ᵐ z ∂ν,‖(I z-F z)*U z‖≤CI+CF := by
    filter_upwards [hIb,hFb,hUn] with z hi hf hu
    rw [norm_mul]
    have hd : ‖I z-F z‖≤CI+CF := (norm_sub_le _ _).trans (add_le_add hi hf.2)
    exact (mul_le_mul hd hu (norm_nonneg _) (by linarith)).trans_eq (mul_one _)
  have hIUi : Integrable (fun z => I z*U z) ν :=
    hIi.mul_bdd hU.aestronglyMeasurable hUn
  have hRUi : Integrable (fun z => κ z*F z*(1-U z)) ν := by
    have h := hRi.mul_bdd
      (aestronglyMeasurable_const.sub hU.aestronglyMeasurable) hOneUn
    exact h
  have hDUi : Integrable (fun z => k z*(I z-F z)*U z) ν := by
    have h := hki.mul_bdd
      ((hIi.aestronglyMeasurable.sub hF.aestronglyMeasurable).mul
        hU.aestronglyMeasurable) hDiffUn
    exact h.congr (.of_forall (fun z => by
      simp only [Pi.sub_apply,Pi.mul_apply]
      ring))
  have hCint := weighted_gradient_defect_integrable ν k F (fun _ => 1) a b
    hk hF measurable_const ha hb (hFb.mono (fun z hz => hz.1))
    (.of_forall (fun _ => by norm_num)) hKi hBi
  have hCi : Integrable (fun z => k z*(∑ ij, a ij z*b ij z)) ν :=
    hCint.congr (.of_forall (fun z => by ring))
  exact ⟨hIUi,hRUi,hDUi,hCi⟩

end SlowEquilibration.ConditionedEntrance
