-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteraturePhysicalNormQ
public import SlowEquilibration.SourceSphericalSelfAveraging

/-!
Array-law-measurable directing families in Section 6 of the manuscript.
Only evaluations of the conditional finite overlap laws are required to be
measurable. The directing measures themselves need not form a kernel.
Finite-law measurability and barycenters are consequences of the manuscript's
infinite-array formulation; using only these consequences strengthens the
results. Countable observable null sets handle replica exclusion, and
companion failure detects an atom at zero without integrating its mass.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceDirectingFamilies

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureDirectingFullToScore PureCapturePhysicalFullToScore
open PureCaptureOverlapScoreCoordinates PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalCoarseDiniAssembly DirectingPhysical
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceSphericalSelfAveraging
open scoped Topology BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The conditional finite overlap law, with diagonal one. -/
def conditionalArrayLaw (ν : ProbabilityMeasure H) (m : ℕ) :
    ProbabilityMeasure (FullOverlapCoordinates m) :=
  (Measure.pi (fun _ : Fin m => (ν : Measure H))).toProbabilityMeasure.map
    directingFullOverlapCoordinates

/-- Exactly the observable measurability used below. It imposes no
measurability on evaluations of the Hilbert-space measures. -/
def ArrayLawMeasurable (G : Ω → ProbabilityMeasure H) : Prop :=
  ∀ (m : ℕ) (E : Set (FullOverlapCoordinates m)), MeasurableSet E →
    Measurable (fun ω => (conditionalArrayLaw (G ω) m : Measure _) E)

/-- The finite marginals of the manuscript's barycenter identity. -/
def Represents (d : Measure Ω) (G : Ω → ProbabilityMeasure H)
    (z : FullOverlapLawArray) : Prop :=
  ∀ (m : ℕ) (E : Set (FullOverlapCoordinates m)), MeasurableSet E →
    (z m : Measure _) E = ∫⁻ ω, (conditionalArrayLaw (G ω) m : Measure _) E ∂d

/-- An almost-everywhere conclusion always has a measurable exceptional
null set, even when its predicate involves a nonmeasurable directing family. -/
private theorem measurable_exception {d : Measure Ω} {P : Ω → Prop}
    (hP : ∀ᵐ ω ∂d, P ω) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧ ∀ ω ∉ Z, P ω := by
  obtain ⟨Z, hsub, hZ, hdZ⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  exact ⟨Z, hZ, hdZ, fun ω hω => Classical.byContradiction (fun hn => hω (hsub hn))⟩

/-- A null observable array event has zero conditional mass outside a
measurable null set. No conditional Hilbert-space kernel is used. -/
private theorem conditional_event_zero (d : Measure Ω) (G : Ω → ProbabilityMeasure H)
    (hG : ArrayLawMeasurable G) {z : FullOverlapLawArray} (hrep : Represents d G z)
    (m : ℕ) (E : Set (FullOverlapCoordinates m)) (hE : MeasurableSet E)
    (hz : (z m : Measure _) E = 0) :
    ∀ᵐ ω ∂d, (conditionalArrayLaw (G ω) m : Measure _) E = 0 := by
  exact (lintegral_eq_zero_iff (hG m E hE)).mp ((hrep m E hE).symm.trans hz)

private theorem conditional_equilateral_mass (ν : ProbabilityMeasure H)
    (m : ℕ) (q ρ : ℝ) :
    (conditionalArrayLaw ν m : Measure _) (fullEquilateralEvent m q ρ) =
      Measure.pi (fun _ : Fin m => (ν : Measure H)) (equilateralEvent m q ρ) := by
  unfold conditionalArrayLaw
  rw [ProbabilityMeasure.map_apply' _
    directingFullOverlapCoordinates_continuous.measurable.aemeasurable
    (fullEquilateralEvent_open m q ρ).measurableSet]
  exact congrArg _ (directingFullOverlapCoordinates_preimage_equilateral m q ρ)

private theorem conditional_cap_mass (ν : ProbabilityMeasure H) (a : ℝ) :
    (conditionalArrayLaw ν 2 : Measure _) (fullPairCapEvent a) =
      Measure.pi (fun _ : Fin 2 => (ν : Measure H)) (pairCapEvent a) := by
  unfold conditionalArrayLaw
  rw [ProbabilityMeasure.map_apply' _
    directingFullOverlapCoordinates_continuous.measurable.aemeasurable
    (fullPairCapEvent_open a).measurableSet]
  exact congrArg _ (directingFullOverlapCoordinates_preimage_pairCap a)

/-- Array-law-measurable version of `lem:dir-exclusion`, before its
physical Portmanteau inputs. In fact no closedness assumption on `A` is
needed: a countable open subcover is chosen before removing null sets. -/
private theorem norms_mem_of_array_exclusion (d : Measure Ω) (G : Ω → ProbabilityMeasure H)
    (hG : ArrayLawMeasurable G) {z : FullOverlapLawArray} (hrep : Represents d G z)
    (A : Set ℝ) (h0 : 0 ∈ A)
    (hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ A →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        (z k : Measure _) (fullEquilateralEvent k q ρ) = 0)
    (hcap : ∃ a < (1 : ℝ), (z 2 : Measure _) (fullPairCapEvent a) = 0) :
    ∀ᵐ ω ∂d, ∀ᵐ v ∂(G ω : Measure H), ‖v‖ ^ 2 ∈ A := by
  classical
  let B : Set ℝ := {q | q ∈ Ioo (0 : ℝ) 1 ∧ q ∉ A}
  choose k ρ hρ hzero using fun q : B => hexclude q.1 q.2.1 q.2.2
  let U : B → Set ℝ := fun q => {r | |r - q.1| < ρ q}
  have hUopen : ∀ q, IsOpen (U q) := fun q =>
    isOpen_lt (continuous_id.sub continuous_const).abs continuous_const
  have hcover : B ⊆ ⋃ q : B, U q := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, by simpa [U] using hρ ⟨q, hq⟩⟩
  obtain ⟨C, hCcount, hCcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof B).elim_countable_subcover U hUopen hcover
  let _ : Countable C := hCcount.to_subtype
  have haeC : ∀ᵐ ω ∂d, ∀ q : C,
      Measure.pi (fun _ : Fin (k q.1) => (G ω : Measure H))
        (equilateralEvent (k q.1) q.1.1 (ρ q.1)) = 0 := by
    apply ae_all_iff.mpr
    intro q
    simpa only [conditional_equilateral_mass] using conditional_event_zero d G hG hrep
      (k q.1) _ (fullEquilateralEvent_open _ _ _).measurableSet (hzero q.1)
  obtain ⟨a, ha, hcapzero⟩ := hcap
  have haeCap : ∀ᵐ ω ∂d,
      Measure.pi (fun _ : Fin 2 => (G ω : Measure H)) (pairCapEvent a) = 0 := by
    simpa only [conditional_cap_mass] using conditional_event_zero d G hG hrep
      2 _ (fullPairCapEvent_open a).measurableSet hcapzero
  filter_upwards [haeC, haeCap] with ω hωC hωCap
  filter_upwards [(G ω : Measure H).support_mem_ae] with v hv
  by_contra hA
  have hq0 : 0 < ‖v‖ ^ 2 := by
    have hqne : ‖v‖ ^ 2 ≠ 0 := fun hz => hA (hz ▸ h0)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hqne)
  have hq1 : ‖v‖ ^ 2 < 1 := (norm_sq_le_of_cap_zero _ hωCap hv).trans_lt ha
  obtain ⟨q, hqC, hnear⟩ := mem_iUnion₂.mp (hCcover ⟨⟨hq0, hq1⟩, hA⟩)
  exact norm_not_near_of_equilateral_zero _ (hωC ⟨q, hqC⟩) hv hnear

private theorem mass_one_of_ae (ν : ProbabilityMeasure H) (S : Set H)
    (hS : ∀ᵐ v ∂(ν : Measure H), v ∈ S) : (ν : Measure H) S = 1 := by
  calc
    (ν : Measure H) S = (ν : Measure H) univ :=
      measure_congr (hS.mono fun v hv => by simp [hv])
    _ = 1 := measure_univ

/-- Literal `lem:dir-exclusion` for every array-law-measurable family.
The physical near-one cap is proved, not an extra hypothesis. The source's
relative closedness and `A ⊆ [0,1)` are unnecessary for this stronger result. -/
private theorem physical_directing_exclusion (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (d : Measure Ω) (G : Ω → ProbabilityMeasure H) (hG : ArrayLawMeasurable G)
    {z : FullOverlapLawArray} (hz : z ∈ physicalFullAsymptoticLimitSet μ β)
    (hrep : Represents d G z) (A : Set ℝ) (h0 : 0 ∈ A)
    (hdecay : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ A →
      ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ => (physicalFullOverlapLaw (n := n) (m := k) μ β :
          Measure _) (fullEquilateralEvent k q ρ)) atTop (𝓝 0)) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (G ω : Measure H) {v | ‖v‖ ^ 2 ∈ A} = 1 := by
  have he : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ A → ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
      (z k : Measure _) (fullEquilateralEvent k q ρ) = 0 := by
    intro q hq hqA
    obtain ⟨k, _, ρ, hρ, hd⟩ := hdecay q hq hqA
    exact ⟨k, ρ, hρ, asymptoticFullOverlapLaw_equilateral_zero_of_physical_decay
      μ β k q ρ hd hz⟩
  obtain ⟨a, ha, hd⟩ := PureCapturePhysicalNearOneDecay.physical_pair_near_one_decay μ hβ.le
  have hc : (z 2 : Measure _) (fullPairCapEvent a) = 0 :=
    asymptoticFullOverlapLaw_pairCap_zero_of_physical_decay μ β a hd hz
  apply measurable_exception
  exact (norms_mem_of_array_exclusion d G hG hrep A h0 he ⟨a, ha, hc⟩).mono
    fun ω hω => mass_one_of_ae (G ω) _ hω

/-- A nonmeasurable quantity bounded by every member of a measurable
sequence with vanishing integrals vanishes outside a measurable null set.
Neither monotonicity of the sequence nor measurability of that quantity is
required. -/
private theorem lower_bound_zero_of_observable_integrals (d : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (hlim : Tendsto (fun n => ∫⁻ ω, f n ω ∂d) atTop (𝓝 0)) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, ∀ b : ℝ≥0∞, (∀ n, b ≤ f n ω) → b = 0 := by
  have hi : (∫⁻ ω, ⨅ n, f n ω ∂d) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    exact .of_forall fun n => lintegral_mono (fun ω => iInf_le (fun n => f n ω) n)
  have hae := (lintegral_eq_zero_iff (Measurable.iInf hf)).mp hi
  apply measurable_exception
  filter_upwards [hae] with ω hω b hb
  exact le_zero_iff.mp ((le_iInf hb).trans_eq hω)

/-- Observable failure to find even one companion near overlap `Q`. -/
def noCompanion (Q θ : ℝ) (T : ℕ) : Set (FullOverlapCoordinates (T * 1 + 1)) :=
  fullScoreProjection ⁻¹' scoreFailure Q θ

private theorem noCompanion_measurable (Q θ : ℝ) (T : ℕ) :
    MeasurableSet (noCompanion Q θ T) :=
  (scoreFailure_closed Q θ).measurableSet.preimage fullScoreProjection_continuous.measurable

private theorem conditional_noCompanion_mass (ν : ProbabilityMeasure H)
    (Q θ : ℝ) (T : ℕ) :
    (conditionalArrayLaw ν (T * 1 + 1) : Measure _) (noCompanion Q θ T) =
      ((ν : Measure H).prod (Measure.pi (fun _ : Fin T =>
        Measure.pi (fun _ : Fin 1 => (ν : Measure H)))))
        (companionFailureEvent 1 Q θ T) := by
  unfold conditionalArrayLaw
  rw [ProbabilityMeasure.map_apply' _
    directingFullOverlapCoordinates_continuous.measurable.aemeasurable
    (noCompanion_measurable Q θ T)]
  have heq : directingFullOverlapCoordinates ⁻¹' noCompanion Q θ T =
      unflattenDirectingReplicas ⁻¹' (companionFailureEvent (H := H) 1 Q θ T) := by
    ext σ
    change fullScoreProjection (directingFullOverlapCoordinates σ) ∈ scoreFailure Q θ ↔ _
    rw [fullScoreProjection_directing]
    exact Set.ext_iff.mp (directingFailure_eq_scoreFailure_preimage Q θ).symm _
  change Measure.pi (fun _ : Fin (T * 1 + 1) => (ν : Measure H))
    (directingFullOverlapCoordinates ⁻¹' noCompanion Q θ T) = _
  rw [heq, ← Measure.map_apply unflattenDirectingReplicas_measurable
    (companionFailureEvent_closed 1 Q θ T).measurableSet,
    pi_map_unflattenDirectingReplicas]

private theorem origin_le_noCompanion (ν : ProbabilityMeasure H) {Q θ : ℝ}
    (hθQ : θ ≤ Q) (T : ℕ) :
    (ν : Measure H) {0} ≤
      (conditionalArrayLaw ν (T * 1 + 1) : Measure _) (noCompanion Q θ T) := by
  rw [conditional_noCompanion_mass]
  have hsub : ({0} : Set H) ×ˢ univ ⊆ companionFailureEvent 1 Q θ T := by
    rintro ⟨v, σ⟩ ⟨hv, _⟩ b hb
    have hv0 : v = 0 := mem_singleton_iff.mp hv
    have hh := hb.2 (0 : Fin 1)
    simp only [hv0, inner_zero_left, zero_sub, abs_neg] at hh
    exact (not_lt_of_ge (hθQ.trans (le_abs_self Q))) hh
  simpa only [Measure.prod_prod, measure_univ, mul_one] using
    (measure_mono (μ := (ν : Measure H).prod (Measure.pi (fun _ : Fin T =>
      Measure.pi (fun _ : Fin 1 => (ν : Measure H))))) hsub)

/-- Companion extraction removes the origin for arbitrary directing
families, by measurable array events rather than a measurable origin mass. -/
private theorem origin_zero_of_companion_decay (d : Measure Ω) (G : Ω → ProbabilityMeasure H)
    (hG : ArrayLawMeasurable G) {z : FullOverlapLawArray} (hrep : Represents d G z)
    {Q θ : ℝ} (hθQ : θ ≤ Q)
    (hlim : Tendsto (fun T => (z (T * 1 + 1) : Measure _) (noCompanion Q θ T))
      atTop (𝓝 0)) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (G ω : Measure H) {0} = 0 := by
  have hlim' : Tendsto (fun T => ∫⁻ ω,
      (conditionalArrayLaw (G ω) (T * 1 + 1) : Measure _) (noCompanion Q θ T) ∂d)
      atTop (𝓝 0) := by
    simpa only [← hrep _ _ (noCompanion_measurable Q θ _)] using hlim
  obtain ⟨Z, hZ, hdZ, h⟩ := lower_bound_zero_of_observable_integrals d _
    (fun T => hG _ _ (noCompanion_measurable Q θ T)) hlim'
  exact ⟨Z, hZ, hdZ, fun ω hω => h ω hω _ (fun T => origin_le_noCompanion (G ω) hθQ T)⟩

private theorem noCompanion_decay_of_norm_representation
    {Ξ K : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (R : RandomDirectingData Ξ K) {z : FullOverlapLawArray}
    (hrep : ∀ m, z m = directingDataFullLaw R m) {Q θ : ℝ} (hθ : 0 < θ)
    (hQ : ∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω, ‖v‖ ^ 2 = Q) :
    Tendsto (fun T => (z (T * 1 + 1) : Measure _) (noCompanion Q θ T))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hmass (T : ℕ) :
      (z (T * 1 + 1) : Measure _) (noCompanion Q θ T) =
      (R.scoreLaw 1 T : Measure (ScoreCoordinates 1 T)) (scoreFailure Q θ) := by
    rw [hrep, noCompanion, ← ProbabilityMeasure.map_apply' _
      fullScoreProjection_continuous.measurable.aemeasurable
      (scoreFailure_closed Q θ).measurableSet]
    change ((directingFullOverlapLaw R.disorderLaw R.directingKernel (T * 1 + 1)).map
      fullScoreProjection : Measure (ScoreCoordinates 1 T)) _ = _
    rw [directingFullOverlapLaw_map_score]
    rfl
  simp_rw [hmass]
  exact (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    (R.scoreLaw_failure_tendsto_zero 1 hθ hQ)

private theorem remove_origin (ν : ProbabilityMeasure H) {Q : ℝ}
    (htwo : ∀ᵐ v ∂(ν : Measure H), ‖v‖ ^ 2 ∈ ({0, Q} : Set ℝ))
    (hzero : (ν : Measure H) {0} = 0) :
    ∀ᵐ v ∂(ν : Measure H), ‖v‖ ^ 2 = Q := by
  have hnzero : ∀ᵐ v ∂(ν : Measure H), v ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  filter_upwards [htwo, hnzero] with v hv hvne
  rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hv) with h0 | hq
  · exact False.elim (hvne (norm_eq_zero.mp (sq_eq_zero_iff.mp h0)))
  · exact hq

private theorem pair_support (d : Measure Ω) (G : Ω → ProbabilityMeasure H)
    (hG : ArrayLawMeasurable G) {z : FullOverlapLawArray} (hrep : Represents d G z)
    (Q : ℝ) (hpair : ∀ᵐ c ∂(z 2 : Measure (FullOverlapCoordinates 2)),
      c 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) :
    ∀ᵐ ω ∂d, ∀ᵐ v ∂(G ω : Measure H), ∀ᵐ w ∂(G ω : Measure H),
      inner ℝ v w ∈ ({-Q, 0, Q} : Set ℝ) := by
  let E : Set (FullOverlapCoordinates 2) := {c | c 0 1 ∉ ({-Q, 0, Q} : Set ℝ)}
  have hE : MeasurableSet E :=
    (((Set.toFinite ({-Q, 0, Q} : Set ℝ)).isClosed.preimage
      ((continuous_apply 1).comp (continuous_apply 0))).measurableSet).compl
  have hz : (z 2 : Measure _) E = 0 := ae_iff.mp hpair
  filter_upwards [conditional_event_zero d G hG hrep 2 E hE hz] with ω hω
  have ha : ∀ᵐ c ∂(conditionalArrayLaw (G ω) 2 : Measure (FullOverlapCoordinates 2)),
      c 0 1 ∈ ({-Q, 0, Q} : Set ℝ) := ae_iff.mpr hω
  have hp : ∀ᵐ σ ∂Measure.pi (fun _ : Fin 2 => (G ω : Measure H)),
      inner ℝ (σ 0) (σ 1) ∈ ({-Q, 0, Q} : Set ℝ) := by
    change ∀ᵐ c ∂(Measure.pi (fun _ : Fin 2 => (G ω : Measure H))).map
      directingFullOverlapCoordinates, c 0 1 ∈ ({-Q, 0, Q} : Set ℝ) at ha
    have hgood : MeasurableSet {c : FullOverlapCoordinates 2 |
        c 0 1 ∈ ({-Q, 0, Q} : Set ℝ)} :=
      ((Set.toFinite ({-Q, 0, Q} : Set ℝ)).isClosed.preimage
        ((continuous_apply 1).comp (continuous_apply 0))).measurableSet
    have ht := (ae_map_iff directingFullOverlapCoordinates_continuous.measurable.aemeasurable
      hgood).mp ha
    simpa only [directingFullOverlapCoordinates, show (0 : Fin 2) ≠ 1 by decide,
      ite_false] using ht
  have hprod : ∀ᵐ p ∂(G ω : Measure H).prod (G ω : Measure H),
      inner ℝ p.1 p.2 ∈ ({-Q, 0, Q} : Set ℝ) := by
    rw [← (measurePreserving_finTwoArrow (G ω : Measure H)).map_eq]
    exact (ae_map_iff (MeasurableEquiv.finTwoArrow.measurable.aemeasurable)
      (((Set.toFinite ({-Q, 0, Q} : Set ℝ)).isClosed.preimage
        (continuous_fst.inner continuous_snd)).measurableSet)).mpr hp
  exact Measure.ae_ae_of_ae_prod hprod

open PureCapturePhysicalInfiniteArrayTightness
open PureCapturePhysicalInfiniteAsymptoticLift

/-- The actual IID infinite directing array, including its diagonal-one
convention. The unit-ball condition below places its entries in `[-1,1]`. -/
def infiniteDirectingCoordinates (v : ℕ → H) : InfiniteOverlapCoordinates :=
  fun i j => if i = j then 1 else inner ℝ (v i) (v j)

private theorem infiniteDirectingCoordinates_measurable :
    Measurable (infiniteDirectingCoordinates (H := H)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hij : i = j
  · simp [infiniteDirectingCoordinates, hij]
  · simpa [infiniteDirectingCoordinates, hij] using
      (measurable_pi_apply i).inner (measurable_pi_apply j)

def conditionalInfiniteLaw (ν : ProbabilityMeasure H) :
    ProbabilityMeasure InfiniteOverlapCoordinates :=
  (Measure.infinitePi (fun _ : ℕ => (ν : Measure H))).toProbabilityMeasure.map
    infiniteDirectingCoordinates

/-- The manuscript's directing-family data: measurable array laws and
their barycenter, with no measurable-measure-valued-kernel assumption. -/
structure DirectingFamily (d : Measure Ω)
    (L : ProbabilityMeasure InfiniteOverlapCoordinates) where
  measure : Ω → ProbabilityMeasure H
  unitBall : ∀ ω, ∀ᵐ v ∂(measure ω : Measure H), ‖v‖ ≤ 1
  array_measurable : ∀ E : Set InfiniteOverlapCoordinates, MeasurableSet E →
    Measurable (fun ω => (conditionalInfiniteLaw (measure ω) : Measure _) E)
  barycenter : ∀ E : Set InfiniteOverlapCoordinates, MeasurableSet E →
    (L : Measure _) E = ∫⁻ ω, (conditionalInfiniteLaw (measure ω) : Measure _) E ∂d

private theorem conditionalInfiniteLaw_finite (ν : ProbabilityMeasure H) (m : ℕ) :
    (conditionalInfiniteLaw ν).map (infiniteTruncate m) = conditionalArrayLaw ν m := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((Measure.infinitePi (fun _ : ℕ => (ν : Measure H))).map
    infiniteDirectingCoordinates).map (infiniteTruncate m) =
      (Measure.pi (fun _ : Fin m => (ν : Measure H))).map directingFullOverlapCoordinates
  rw [Measure.map_map (infiniteTruncate_continuous m).measurable
    infiniteDirectingCoordinates_measurable]
  have hfun : infiniteTruncate m ∘ infiniteDirectingCoordinates (H := H) =
      directingFullOverlapCoordinates (H := H) ∘ OverlapPaper.firstFiniteSamples (E := H) m := by
    ext v i j
    simp only [Function.comp_apply, infiniteTruncate, infiniteDirectingCoordinates,
      directingFullOverlapCoordinates, OverlapPaper.firstFiniteSamples, Fin.val_inj]
  rw [hfun, ← Measure.map_map directingFullOverlapCoordinates_continuous.measurable
    (OverlapPaper.measurable_firstFiniteSamples m), OverlapPaper.infiniteIID_firstFiniteSamples]
  rfl

private theorem DirectingFamily.finite_measurable
    {d : Measure Ω} {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (F : DirectingFamily (H := H) d L) : ArrayLawMeasurable F.measure := by
  intro m E hE
  have hmap (ω : Ω) : (conditionalArrayLaw (F.measure ω) m : Measure _) E =
      (conditionalInfiniteLaw (F.measure ω) : Measure _) (infiniteTruncate m ⁻¹' E) := by
    rw [← conditionalInfiniteLaw_finite, ProbabilityMeasure.map_apply' _
      (infiniteTruncate_continuous m).measurable.aemeasurable hE]
  simp_rw [hmap]
  exact F.array_measurable _ (hE.preimage (infiniteTruncate_continuous m).measurable)

private theorem DirectingFamily.finite_represents
    {d : Measure Ω} {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (F : DirectingFamily (H := H) d L) : Represents d F.measure (infiniteToFullLawArray L) := by
  intro m E hE
  have hmap (ω : Ω) : (conditionalArrayLaw (F.measure ω) m : Measure _) E =
      (conditionalInfiniteLaw (F.measure ω) : Measure _) (infiniteTruncate m ⁻¹' E) := by
    rw [← conditionalInfiniteLaw_finite, ProbabilityMeasure.map_apply' _
      (infiniteTruncate_continuous m).measurable.aemeasurable hE]
  simp_rw [hmap]
  change (L.map (infiniteTruncate m) : Measure _) E = _
  rw [ProbabilityMeasure.map_apply' _
    (infiniteTruncate_continuous m).measurable.aemeasurable hE]
  exact F.barycenter _ (hE.preimage (infiniteTruncate_continuous m).measurable)

/-- `lem:dir-exclusion`, with the literal infinite-array family quantifier
and a measurable exceptional null set. Relative closedness can be omitted. -/
theorem directing_exclusion (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (d : Measure Ω) [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L) (A : Set ℝ) (h0 : 0 ∈ A)
    (hdecay : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ A →
      ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ => (physicalFullOverlapLaw (n := n) (m := k) μ β :
          Measure _) (fullEquilateralEvent k q ρ)) atTop (𝓝 0)) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (F.measure ω : Measure H) {v | ‖v‖ ^ 2 ∈ A} = 1 :=
  physical_directing_exclusion μ hβ d F.measure F.finite_measurable
    (infiniteToFullLawArray_maps_asymptotic_limits μ β hL) F.finite_represents A h0 hdecay

/-- `thm:dir-norm` for every manuscript directing family of every
physical limiting array. All physical premises are discharged from the
certificate and the four explicit literature interfaces. -/
theorem directing_norm (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (d : Measure Ω) [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (F.measure ω : Measure H) {v | ‖v‖ ^ 2 = Q} = 1 := by
  let z := infiniteToFullLawArray L
  have hz := infiniteToFullLawArray_maps_asymptotic_limits μ β hL
  have he := LiteratureSubagFullOverlapAdapter.physical_full_overlap_exclusion_of_offContactTAPGap
    _ h5 h25 (strictTAPGap_of_literature hChen hChenSen h _)
  have he' : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ ({0, Q} : Set ℝ) →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        (z k : Measure _) (fullEquilateralEvent k q ρ) = 0 := by
    intro q hq hqA
    obtain ⟨k, ρ, hρ, hd⟩ := he q hq (fun hqQ => hqA (by simp [hqQ]))
    exact ⟨k, ρ, hρ, asymptoticFullOverlapLaw_equilateral_zero_of_physical_decay
      μ β k q ρ hd hz⟩
  obtain ⟨a, ha, hd⟩ := PureCapturePhysicalNearOneDecay.physical_pair_near_one_decay μ h.beta_pos.le
  have htwo := norms_mem_of_array_exclusion d F.measure F.finite_measurable F.finite_represents
    ({0, Q} : Set ℝ) (by simp) he'
    ⟨a, ha, asymptoticFullOverlapLaw_pairCap_zero_of_physical_decay μ β a hd hz⟩
  obtain ⟨R, hrep, hball⟩ :=
    PureCapturePhysicalDSFiniteBridge.physicalFullAsymptoticLimit_randomDirecting μ β hz
  have hnorm := SourceLiteraturePhysicalNormQ.physicalDirectingNormQ_of_cited_theorems
    hChen hChenSen h h5 h25 z hz R hrep hball
  obtain ⟨Z, hZ, hdZ, hzero⟩ := origin_zero_of_companion_decay d F.measure
    F.finite_measurable F.finite_represents (show Q / 2 ≤ Q by linarith [h.overlap_range.1])
    (noCompanion_decay_of_norm_representation R hrep
      (show 0 < Q / 2 by linarith [h.overlap_range.1]) hnorm)
  have hz0 : ∀ᵐ ω ∂d, (F.measure ω : Measure H) {0} = 0 := by
    filter_upwards [show ∀ᵐ ω ∂d, ω ∉ Z from ae_iff.mpr (by simpa using hdZ)] with ω hω
    exact hzero ω hω
  apply measurable_exception
  filter_upwards [htwo, hz0] with ω hω hω0
  exact mass_one_of_ae (F.measure ω) _ (remove_origin (F.measure ω) hω hω0)

/-- `prop:dir-even`(2), including the literal sum of countably many
positive-mass atoms, for every array-law-measurable directing family.
Only Chen's interface is needed; the ground-state and Subag interfaces
are discharged by the proved three-degree rigidity argument. -/
theorem directing_even (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (heven : ∀ p ∈ μ.coeff.support, Even p) (hcard : 3 ≤ μ.coeff.support.card)
    (d : Measure Ω) [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L) :
    ThreePointPairLaw (infiniteToFullLawArray L) x Q ∧
      ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
        ∀ ω ∉ Z, CountablyAtomicAt (F.measure ω : Measure H) Q := by
  have hz := infiniteToFullLawArray_maps_asymptotic_limits μ β hL
  obtain ⟨hpair, _, R, hrep, hR⟩ := source_even_three_degree_directing
    (Ξ := ProbabilityMeasure OverlapPaper.DSHilbert) (H := OverlapPaper.DSHilbert)
    hChen μ h heven hcard hz
  have hnorm : ∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω, ‖v‖ ^ 2 = Q := by
    filter_upwards [hR] with ω hω
    have hs : ∀ᵐ v ∂ R.directingKernel ω, v ∈ (R.directingKernel ω).support :=
      (R.directingKernel ω).support_mem_ae
    exact hs.mono fun v hv => (hω.2.2.2.1 v hv).2
  have hp := pair_support d F.measure F.finite_measurable F.finite_represents Q hpair.1
  have htwo : ∀ᵐ ω ∂d, ∀ᵐ v ∂(F.measure ω : Measure H),
      ‖v‖ ^ 2 ∈ ({0, Q} : Set ℝ) := by
    filter_upwards [hp] with ω hω
    have hs := PureCaptureAtomicDirectingGeometry.inner_on_support_of_pair_support _ Q hω
    filter_upwards [(F.measure ω : Measure H).support_mem_ae] with v hv
    have hh := hs v hv v hv
    rw [real_inner_self_eq_norm_sq] at hh
    simp only [mem_insert_iff, mem_singleton_iff] at hh ⊢
    rcases hh with hn | h0 | hq
    · nlinarith [sq_nonneg ‖v‖, h.overlap_range.1]
    · exact Or.inl h0
    · exact Or.inr hq
  obtain ⟨Z, _, hdZ, hzero⟩ := origin_zero_of_companion_decay d F.measure
    F.finite_measurable F.finite_represents (show Q / 2 ≤ Q by linarith [h.overlap_range.1])
    (noCompanion_decay_of_norm_representation R hrep
      (show 0 < Q / 2 by linarith [h.overlap_range.1]) hnorm)
  have hz0 : ∀ᵐ ω ∂d, (F.measure ω : Measure H) {0} = 0 := by
    filter_upwards [show ∀ᵐ ω ∂d, ω ∉ Z from ae_iff.mpr (by simpa using hdZ)] with ω hω
    exact hzero ω hω
  refine ⟨hpair, measurable_exception ?_⟩
  filter_upwards [htwo, hz0, hp] with ω hω hω0 hωpair
  have ha := PureCaptureAtomicDirectingGeometry.countable_atomic_support
    (F.measure ω : Measure H) h.overlap_range.1 (remove_origin (F.measure ω) hω hω0) hωpair
  exact ⟨PureCaptureAtomicDirectingGeometry.eq_sum_smul_dirac_support_of_countable _ ha.1, ha⟩

end SlowEquilibration.SourceDirectingFamilies
