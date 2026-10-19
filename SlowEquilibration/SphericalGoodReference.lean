-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOverlapPartitionMeasurable
public import SlowEquilibration.SphericalLikelihoodTransfer

@[expose] public section

/-! Actual Gibbs-reference disintegration and the good-set Markov estimate.
The good set is Borel, lies on the physical sphere, and is constructed from
the actual joint bad-reference event, not from assumed Gibbs mass bounds. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def referenceBadMass {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (E : Set (Disorder N P × Vector N)) (J : Disorder N P) : ℝ :=
  (gibbsLaw N β (field c J)).real {u | (J,u) ∈ E}

theorem referenceBadMass_eq_integral {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ)
    {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) (J : Disorder N P) :
    referenceBadMass c β E J = ∫ u,
      E.indicator (fun z => gibbsDensity N β (field c z.1) z.2) (J,u) ∂sphereLaw N := by
  have hsection : MeasurableSet {u : Vector N | (J,u) ∈ E} :=
    hE.preimage (measurable_const.prodMk measurable_id)
  rw [referenceBadMass,gibbsLaw_real_eq_partitionOn_div hN β (field_contDiff c J).continuous hsection]
  unfold partitionOn
  rw [← integral_div]
  have heq : (fun u => E.indicator (fun z => gibbsDensity N β (field c z.1) z.2) (J,u)) =
      {u : Vector N | (J,u) ∈ E}.indicator (fun u => Real.exp (β*field c J u)/partition N β (field c J)) := by
    funext u
    by_cases hu : (J,u) ∈ E <;> simp [hu,gibbsDensity]
  rw [heq,integral_indicator hsection]

theorem referenceBadMass_measurable {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ)
    {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) :
    Measurable (referenceBadMass c β E) := by
  have hm := ((gibbsReferenceDensity_measurable c β).stronglyMeasurable.indicator hE).integral_prod_right'
    (ν := sphereLaw N) |>.measurable
  convert hm using 1
  funext J
  exact referenceBadMass_eq_integral hN c β hE J

theorem referenceBadMass_integrable {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ)
    {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) :
    Integrable (referenceBadMass c β E) (disorderLaw N P) := by
  apply Integrable.of_bound (referenceBadMass_measurable hN c β hE).aestronglyMeasurable 1
  exact .of_forall fun J => by
    let _ := gibbsLaw_probability hN β (field_contDiff c J).continuous
    unfold referenceBadMass
    rw [Real.norm_eq_abs,abs_of_nonneg (measureReal_nonneg)]
    exact measureReal_le_one

/-- Exact disintegration of the actual Gibbs-reference joint law. -/
theorem gibbsReference_real_eq_integral_badMass {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) :
    (gibbsReferenceLaw c β).real E =
      ∫ J, referenceBadMass c β E J ∂disorderLaw N P := by
  have hi := gibbsReferenceDensity_integrable hN c β
  have hpos : ∀ z : Disorder N P × Vector N, 0 ≤ gibbsDensity N β (field c z.1) z.2 :=
    fun z => (gibbsDensity_pos hN β (field_contDiff c z.1).continuous z.2).le
  have heq : (gibbsReferenceLaw c β).real E =
      ∫ z in E, gibbsDensity N β (field c z.1) z.2 ∂(disorderLaw N P).prod (sphereLaw N) := by
    unfold Measure.real
    rw [gibbsReferenceLaw,withDensity_apply _ hE,
      ← ofReal_integral_eq_lintegral_ofReal hi.restrict (.of_forall hpos),
      ENNReal.toReal_ofReal (integral_nonneg hpos)]
  rw [heq,← integral_indicator hE,integral_prod _ (hi.indicator hE)]
  apply integral_congr_ae
  exact .of_forall fun J => (referenceBadMass_eq_integral hN c β hE J).symm

theorem goodReferenceSet_compl_mass_eq {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ)
    (E : Set (Disorder N P × Vector N)) (J : Disorder N P) :
    (gibbsLaw N β (field c J)).real (goodReferenceSet E J)ᶜ = referenceBadMass c β E J := by
  unfold referenceBadMass Measure.real
  congr 1
  apply measure_congr
  filter_upwards [gibbsLaw_support hN β (field c J)] with u hu
  simp only [goodReferenceSet,mem_compl_iff,mem_ofPred_eq,hu,true_and,not_not]

/-- The genuine good-reference Markov estimate, with exact finite-volume
constant. Combined with likelihood transfer this gives the quenched good set. -/
theorem goodReferenceSet_failure_le {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ)
    {E : Set (Disorder N P × Vector N)} (hE : MeasurableSet E) {a : ℝ} (ha : 0 < a) :
    (disorderLaw N P).real {J | a < (gibbsLaw N β (field c J)).real (goodReferenceSet E J)ᶜ} ≤
      (gibbsReferenceLaw c β).real E/a := by
  let B : Set (Disorder N P) := {J | a < referenceBadMass c β E J}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (referenceBadMass_measurable hN c β hE)
  have hpoint : ∀ᵐ J ∂disorderLaw N P,
      B.indicator (fun _ => a) J ≤ referenceBadMass c β E J := .of_forall fun J => by
    by_cases hJ : J ∈ B
    · rw [indicator_of_mem hJ]
      exact le_of_lt hJ
    · rw [indicator_of_notMem hJ]
      exact measureReal_nonneg
  have hh := integral_mono_ae ((integrable_const a).indicator hB)
    (referenceBadMass_integrable hN c β hE) hpoint
  rw [integral_indicator_const a hB,← gibbsReference_real_eq_integral_badMass hN c β hE] at hh
  simp only [smul_eq_mul] at hh
  have htail : (disorderLaw N P).real B ≤ (gibbsReferenceLaw c β).real E/a :=
    (le_div_iff₀ ha).mpr (by linarith)
  simpa only [goodReferenceSet_compl_mass_eq hN c β E] using htail

end
end SlowEquilibration.SphericalModel
