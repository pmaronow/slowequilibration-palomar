-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbsMass
public import SlowEquilibration.SphericalTruncatedPartition

@[expose] public section

/-! Borel overlap-restricted partitions for actual disorder and reference
points. These give genuine measurable bad-reference events for likelihood
transfer and Gibbs disintegration in the good-reference proposition. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def overlapRestrictedPartition {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) (A : Set ℝ)
    (z : Disorder N P × Vector N) : ℝ :=
  partitionOn β (field c z.1) {x | overlap x z.2 ∈ A}

theorem overlapRestrictedPartition_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) : Measurable (overlapRestrictedPartition (N := N) c β A) := by
  let B : Set ((Disorder N P × Vector N) × Vector N) := {z | overlap z.2 z.1.2 ∈ A}
  have hB : MeasurableSet B := hA.preimage (by unfold overlap; fun_prop)
  have hc : Continuous (fun z : (Disorder N P × Vector N) × Vector N => Real.exp (β*field c z.1.1 z.2)) :=
    Real.continuous_exp.comp (((field_jointContinuous c).comp
      (continuous_fst.fst.prodMk continuous_snd)).const_mul β)
  have hm := (hc.stronglyMeasurable.indicator hB).integral_prod_right' (ν := sphereLaw N) |>.measurable
  convert hm using 1
  funext z
  unfold overlapRestrictedPartition partitionOn
  have hsection : MeasurableSet {x : Vector N | overlap x z.2 ∈ A} :=
    hA.preimage (by unfold overlap; fun_prop)
  rw [← integral_indicator hsection]
  apply integral_congr_ae
  exact .of_forall fun x => by
    by_cases hx : overlap x z.2 ∈ A <;> simp [B,hx]

def badReferenceEvent {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (A B C : Set ℝ) (capUpper coreLower collarUpper : ℝ) : Set (Disorder N P × Vector N) :=
  {z | capUpper < overlapRestrictedPartition c β A z ∨ overlapRestrictedPartition c β B z < coreLower ∨
    collarUpper < overlapRestrictedPartition c β C z}

theorem badReferenceEvent_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (capUpper coreLower collarUpper : ℝ) :
    MeasurableSet (badReferenceEvent (N := N) c β A B C capUpper coreLower collarUpper) := by
  exact (measurableSet_lt measurable_const (overlapRestrictedPartition_measurable (N := N) c β hA)).union
    ((measurableSet_lt (overlapRestrictedPartition_measurable (N := N) c β hB) measurable_const).union
      (measurableSet_lt measurable_const (overlapRestrictedPartition_measurable (N := N) c β hC)))

def goodReferenceSet {N P : ℕ} (E : Set (Disorder N P × Vector N)) (J : Disorder N P) : Set (Vector N) :=
  {u | ‖u‖^2=(N : ℝ) ∧ (J,u) ∉ E}

theorem goodReferenceSet_measurable {N P : ℕ} {E : Set (Disorder N P × Vector N)}
    (hE : MeasurableSet E) (J : Disorder N P) : MeasurableSet (goodReferenceSet E J) := by
  exact (isClosed_eq (continuous_norm.pow 2) continuous_const).measurableSet.inter
    ((hE.preimage (measurable_const.prodMk measurable_id)).compl)

theorem goodReferenceSet_subset_sphere {N P : ℕ} (E : Set (Disorder N P × Vector N)) (J : Disorder N P) :
    goodReferenceSet E J ⊆ {u : Vector N | ‖u‖^2=(N : ℝ)} := fun _ hu => hu.1

end
end SlowEquilibration.SphericalModel
