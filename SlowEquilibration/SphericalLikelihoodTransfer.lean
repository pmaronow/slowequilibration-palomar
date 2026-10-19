-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PlantedLaw
public import SlowEquilibration.SphericalParisiBound
public import SlowEquilibration.SphericalConcentration

/-! Quantitative transfer between the actual planted and Gibbs-reference
joint laws. The finite-dimensional likelihood estimate is unconditional;
thermodynamic replica-symmetric concentration is a separate input. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gibbsReference_eq_planted_inverse_likelihood {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    gibbsReferenceLaw (N := N) c β = (plantedLaw c β).withDensity
      (fun z => (ENNReal.ofReal (likelihood c β z.1))⁻¹) := by
  rw [planted_eq_gibbsReference_withDensity hN c β]
  symm
  apply withDensity_inv_same
  · exact ((likelihood_measurable c β).comp measurable_fst).ennreal_ofReal
  · exact .of_forall fun z => (ENNReal.ofReal_pos.mpr (likelihood_pos hN c β z.1)).ne'
  · exact .of_forall fun _ => ENNReal.ofReal_ne_top

/-- A literal finite-volume likelihood split, for every Borel event and
every real cutoff. Both measures are the actual field/reference laws. -/
theorem gibbsReference_event_le_likelihood_split {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β τ : ℝ)
    {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) :
    (gibbsReferenceLaw c β).real E ≤
      (disorderLaw N P).real {J | likelihood c β J < Real.exp (-τ)} +
        Real.exp τ * (plantedLaw c β).real E := by
  let Q := gibbsReferenceLaw (N := N) c β
  let P₀ := plantedLaw (N := N) c β
  let B : Set (Disorder N P × Vector N) := {z | likelihood c β z.1 < Real.exp (-τ)}
  let G := E \ B
  let : IsProbabilityMeasure Q := gibbsReferenceLaw_probability hN c β
  let : IsProbabilityMeasure P₀ := plantedLaw_probability hN c hc β
  have hB : MeasurableSet B := measurableSet_lt
    ((likelihood_measurable c β).comp measurable_fst) measurable_const
  have hG : MeasurableSet G := hE.diff hB
  have hsplit : Q.real E ≤ Q.real B + Q.real G := by
    refine (measureReal_mono (show E ⊆ B ∪ G from fun z hz => ?_)).trans
      (measureReal_union_le _ _)
    by_cases hzB : z ∈ B
    · exact Or.inl hzB
    · exact Or.inr ⟨hz, hzB⟩
  have hweight : Q G ≤ ENNReal.ofReal (Real.exp τ) * P₀ E := by
    rw [show Q = P₀.withDensity (fun z => (ENNReal.ofReal (likelihood c β z.1))⁻¹) from
      gibbsReference_eq_planted_inverse_likelihood hN c β, withDensity_apply _ hG]
    calc
      _ ≤ ∫⁻ _ in G, ENNReal.ofReal (Real.exp τ) ∂P₀ := by
        apply setLIntegral_mono' hG
        intro z hz
        have hL : Real.exp (-τ) ≤ likelihood c β z.1 := not_lt.mp hz.2
        have hi := ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hL)
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg] at hi
        simpa only [neg_neg] using hi
      _ = ENNReal.ofReal (Real.exp τ) * P₀ G := setLIntegral_const _ _
      _ ≤ _ := by
        have hGE : P₀ G ≤ P₀ E := measure_mono (show G ⊆ E from Set.sdiff_subset)
        gcongr
  have hweightReal : Q.real G ≤ Real.exp τ * P₀.real E := by
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P₀ E)) hweight
    simpa only [Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos τ).le] using ht
  have hbad : Q.real B = (disorderLaw N P).real {J | likelihood c β J < Real.exp (-τ)} := by
    have hs : MeasurableSet {J : Disorder N P | likelihood c β J < Real.exp (-τ)} :=
      measurableSet_lt (likelihood_measurable c β) measurable_const
    simp only [Measure.real]
    rw [← gibbsReference_disorder_marginal hN c β, Measure.map_apply measurable_fst hs]
    rfl
  exact hsplit.trans (by rw [hbad]; linarith)

theorem likelihood_lt_exp_iff_logPartition {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β τ : ℝ) (J : Disorder N P) :
    likelihood c β J < Real.exp (-τ) ↔
      Real.log (partition N β (field c J)) < annealedExponent N c β - τ := by
  unfold likelihood
  rw [← Real.exp_log (partition_pos hN β (field_contDiff c J).continuous),
    ← Real.exp_add, Real.exp_lt_exp, Real.log_exp]
  constructor <;> intro h <;> linarith

theorem gibbsReference_event_le_logPartition_split {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β τ : ℝ)
    {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) :
    (gibbsReferenceLaw c β).real E ≤
      (disorderLaw N P).real {J | Real.log (partition N β (field c J)) <
        annealedExponent N c β - τ} + Real.exp τ * (plantedLaw c β).real E := by
  simpa only [likelihood_lt_exp_iff_logPartition hN c β τ] using
    gibbsReference_event_le_likelihood_split hN c hc β τ hE

end
end SlowEquilibration.SphericalModel
