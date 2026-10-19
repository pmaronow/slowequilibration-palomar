-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagTAP

@[expose] public section

/-!
# Full-sequence exclusion at a noncontact TAP gap

Remark 25 following Subag's Theorem 3 (arXiv:1804.10576v6) says that
vanishing logarithmic rate along a subsequence, for every replica count
and tolerance, already implies full multisamplability.  Its contrapositive,
combined with the universal upper bound that an annealed Gibbs event has
probability at most one, gives a *fixed* count and tolerance with an
exponential upper bound along the full dimension sequence.  We state that
published consequence as an explicit hypothesis and apply Theorem 5 to
exclude a point where the physical TAP value has a strict gap.
-/

namespace SlowEquilibration.LiteratureSubagReplicaExclusion

noncomputable section
open MeasureTheory Filter Set
open LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open scoped Topology
set_option autoImplicit false

/-- Full-sequence contrapositive of Subag's Remark 25.  The conclusion is
about the original annealed Gibbs event of Definition 2, not a perturbed
array or a chosen subsequence.  This is an explicit cited theorem argument. -/
def Remark25Contrapositive (μ : FiniteMixture) (β : ℝ) : Prop :=
  0 < β ∧ ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → ¬ MultiSamplable μ β q →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤
          Real.exp (-c * (N : ℝ))

/-- The physical strict TAP gap and Subag's Theorem 5 and Remark 25 imply
the full-sequence, exponential equilateral-replica exclusion needed in the
manuscript's directing-measure proof. -/
theorem exponential_exclusion_of_strictTAPGap
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D) (h25 : Remark25Contrapositive μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hgap : tapValue D q < D.pressure) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤
          Real.exp (-c * (N : ℝ)) :=
  h25.2 q hq (not_multiSamplable_of_strictTAPGap D h5 hq hgap)

/-- Any fixed exponential equilateral bound tends to zero.  This is the
analytic part of the adapter to physical overlap-array exclusion. -/
theorem expectedOverlapBlockProbability_tendsto_zero_of_exponential
    (μ : FiniteMixture) (β q ρ c : ℝ) (k : ℕ) (hc : 0 < c)
    (hbound : ∀ᶠ N : ℕ in atTop,
      expectedOverlapBlockProbability N k μ β q ρ ≤
        Real.exp (-c * (N : ℝ))) :
    Tendsto (fun N : ℕ => expectedOverlapBlockProbability N k μ β q ρ)
      atTop (nhds (0 : ℝ)) := by
  have hdecay : Tendsto (fun N : ℕ => Real.exp (-c * (N : ℝ)))
      atTop (nhds (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  apply squeeze_zero' (.of_forall fun N => measureReal_nonneg) hbound hdecay

/-- The same cited inputs provide vanishing physical equilateral mass;
the explicit exponential rate remains available to downstream proofs. -/
theorem equilateral_mass_tendsto_zero_of_strictTAPGap
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D) (h25 : Remark25Contrapositive μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hgap : tapValue D q < D.pressure) :
    ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => expectedOverlapBlockProbability N k μ β q ρ)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨k,_hk,ρ,hρ,c,hc,hbound⟩ :=
    exponential_exclusion_of_strictTAPGap D h5 h25 hq hgap
  exact ⟨k,ρ,hρ,
    expectedOverlapBlockProbability_tendsto_zero_of_exponential μ β q ρ c k hc hbound⟩

end
end SlowEquilibration.LiteratureSubagReplicaExclusion
