-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPalmHolder

@[expose] public section

/-! The event-inclusion and determinant-weighted union step needed after a
physical central-latitude-to-full-band comparison. The comparison hypothesis
is displayed explicitly: this file is an assembly lemma, not a proof of that
still-missing physical curvature/coarea estimate. -/

namespace SlowEquilibration.SphericalTAPCriticalPalmAssembly
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
set_option maxHeartbeats 400000

/-- If a full band dominates its central normalized residual partition on a
regularity event, its Palm lower tail is bounded by the regularity failure
and residual lower tails. The weight `D` may be correlated with both events. -/
theorem palm_band_tail_le_regular_and_residual
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (D band residual : Ω → ℝ) (bad : Set Ω)
    (hD : Integrable D ν) (hDnonneg : ∀ z, 0 ≤ D z)
    (hDmean : 0 < ∫ z, D z ∂ν)
    (hbad : MeasurableSet bad) (hband : Measurable band)
    (hresidual : Measurable residual)
    {C c scale δ : ℝ} (_hC : 0 ≤ C) (hc : 0 < c)
    (hscale : 0 < scale) (_hδ : 0 < δ)
    (hcomparison : ∀ z ∉ bad, c*scale*residual z ≤ band z)
    (hholder : ∀ A : Set Ω, MeasurableSet A →
      (∫ z in A, D z ∂ν) ≤
        Real.sqrt C*Real.sqrt (ν.real A)*(∫ z, D z ∂ν)) :
    (∫ z in {z | band z < δ*scale}, D z ∂ν) / (∫ z, D z ∂ν) ≤
      Real.sqrt C*(Real.sqrt (ν.real bad)+
        Real.sqrt (ν.real {z | residual z < δ/c})) := by
  let A : Set Ω := {z | band z < δ*scale}
  let B : Set Ω := {z | residual z < δ/c}
  have hA : MeasurableSet A := measurableSet_lt hband measurable_const
  have hB : MeasurableSet B := measurableSet_lt hresidual measurable_const
  have hsub : A ⊆ bad ∪ B := by
    intro z hz
    by_cases h : z ∈ bad
    · exact Or.inl h
    · right
      have hcomp := hcomparison z h
      change residual z < δ/c
      have hraw : c*scale*residual z < δ*scale := lt_of_le_of_lt hcomp hz
      have hraw' : (c*residual z)*scale < δ*scale := by
        nlinarith [hraw]
      have hp : c*residual z < δ := by
        by_contra hnot
        have hle : δ ≤ c*residual z := le_of_not_gt hnot
        have hscale_le := mul_le_mul_of_nonneg_right hle hscale.le
        exact (not_lt_of_ge hscale_le) hraw'
      exact (lt_div_iff₀ hc).mpr (by simpa only [mul_comm] using hp)
  have hUnion : (∫ z in bad ∪ B, D z ∂ν) ≤
      (∫ z in bad, D z ∂ν)+(∫ z in B, D z ∂ν) := by
    have hsplit : bad ∪ B = bad ∪ (B \ bad) := by
      ext z
      simp only [mem_union, mem_sdiff]
      tauto
    rw [hsplit, setIntegral_union disjoint_sdiff_right (hB.diff hbad)
      (hD.restrict (s := bad)) (hD.restrict (s := B \ bad))]
    have hsubset : B \ bad ⊆ B := by
      intro z hz
      exact hz.1
    have hsmall : (∫ z in B \ bad, D z ∂ν) ≤ (∫ z in B, D z ∂ν) :=
      setIntegral_mono_set (hD.restrict (s := B))
        (Filter.Eventually.of_forall (fun z => hDnonneg z))
        (Filter.Eventually.of_forall hsubset)
    exact add_le_add_right hsmall _
  have hmono : (∫ z in A, D z ∂ν) ≤ (∫ z in bad ∪ B, D z ∂ν) :=
    setIntegral_mono_set (hD.restrict (s := bad ∪ B))
      (Filter.Eventually.of_forall (fun z => hDnonneg z))
      (Filter.Eventually.of_forall hsub)
  have hBound : (∫ z in A, D z ∂ν) ≤
      Real.sqrt C*(Real.sqrt (ν.real bad)+Real.sqrt (ν.real B))*
        (∫ z, D z ∂ν) := by
    calc
      _ ≤ (∫ z in bad ∪ B, D z ∂ν) := hmono
      _ ≤ (∫ z in bad, D z ∂ν)+(∫ z in B, D z ∂ν) := hUnion
      _ ≤ Real.sqrt C*Real.sqrt (ν.real bad)*(∫ z, D z ∂ν)+
          Real.sqrt C*Real.sqrt (ν.real B)*(∫ z, D z ∂ν) :=
        add_le_add (hholder bad hbad) (hholder B hB)
      _ = _ := by ring
  exact (div_le_iff₀ hDmean).mpr hBound

end
end SlowEquilibration.SphericalTAPCriticalPalmAssembly
