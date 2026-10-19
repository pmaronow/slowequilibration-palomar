-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGoodReference
public import SlowEquilibration.SphericalCapCoreCollar

@[expose] public section

/-! A genuine finite-volume good-reference event for cap, core and collar
masses. Its failure is bounded by an actual pressure failure probability and
the actual Gibbs-reference partition-test event, with no thermodynamic
formula or Gibbs mass conclusion supplied as a premise. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def capCoreCollarBadEvent {N P : ℕ} (c : Degree P → ℝ) (β F J G δ q₁ q₂ q w : ℝ) :
    Set (Disorder N P × Vector N) :=
  badReferenceEvent c β (Ici q₁) (Icc (q-w) (q+w)) (Icc q₁ q₂)
    (Real.exp ((N : ℝ)*(F-J+δ))) (Real.exp ((N : ℝ)*(F-J-δ)))
    (Real.exp ((N : ℝ)*(F-J-G+δ)))

theorem capCoreCollarBadEvent_measurable {N P : ℕ} (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w : ℝ) :
    MeasurableSet (capCoreCollarBadEvent (N := N) c β F J G δ q₁ q₂ q w) :=
  badReferenceEvent_measurable c β measurableSet_Ici measurableSet_Icc measurableSet_Icc _ _ _

theorem goodReferenceSet_cap_core_collar {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w : ℝ) (D : Disorder N P)
    (hp : |Real.log (partition N β (field c D))/(N : ℝ)-F| ≤ δ)
    {u : Vector N} (hu : u ∈ goodReferenceSet (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w) D) :
    (gibbsLaw N β (field c D)).real (cap u q₁) ≤ Real.exp (-(N : ℝ)*(J-2*δ)) ∧
      Real.exp (-(N : ℝ)*(J+2*δ)) ≤ (gibbsLaw N β (field c D)).real (coreBand u q w) ∧
      (gibbsLaw N β (field c D)).real (collar u q₁ q₂) ≤ Real.exp (-(N : ℝ)*(J+G-2*δ)) := by
  have hbad := hu.2
  change ¬ (Real.exp ((N : ℝ)*(F-J+δ)) < overlapRestrictedPartition c β (Ici q₁) (D,u) ∨
    overlapRestrictedPartition c β (Icc (q-w) (q+w)) (D,u) < Real.exp ((N : ℝ)*(F-J-δ)) ∨
    Real.exp ((N : ℝ)*(F-J-G+δ)) < overlapRestrictedPartition c β (Icc q₁ q₂) (D,u)) at hbad
  have hcap := not_lt.mp (fun hc => hbad (Or.inl hc))
  have hcore := not_lt.mp (fun hc => hbad (Or.inr (Or.inl hc)))
  have hcollar := not_lt.mp (fun hc => hbad (Or.inr (Or.inr hc)))
  change partitionOn β (field c D) (cap u q₁) ≤ _ at hcap
  change Real.exp ((N : ℝ)*(F-J-δ)) ≤ partitionOn β (field c D)
    (overlapRegion u (Icc (q-w) (q+w))) at hcore
  rw [← coreBand_eq_overlapRegion] at hcore
  change partitionOn β (field c D) (collar u q₁ q₂) ≤ _ at hcollar
  exact gibbsLaw_cap_core_collar_bounds hN β (field_contDiff c D).continuous u hp hcap hcore hcollar

def goodCapCoreCollarEvent {N P : ℕ} (c : Degree P → ℝ) (β F J G δ q₁ q₂ q w a : ℝ) :
    Set (Disorder N P) :=
  {D | |Real.log (partition N β (field c D))/(N : ℝ)-F| ≤ δ ∧
    (gibbsLaw N β (field c D)).real
      (goodReferenceSet (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w) D)ᶜ ≤ a}

theorem goodCapCoreCollarEvent_measurable {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w a : ℝ) :
    MeasurableSet (goodCapCoreCollarEvent (N := N) c β F J G δ q₁ q₂ q w a) := by
  have hE := capCoreCollarBadEvent_measurable (N := N) c β F J G δ q₁ q₂ q w
  have hm := referenceBadMass_measurable hN c β hE
  have hlog : Measurable (fun D : Disorder N P => Real.log (partition N β (field c D))/(N : ℝ)-F) :=
    (((partition_measurable (N := N) c β).log.div_const (N : ℝ)).sub_const F)
  have hpressure : Measurable (fun D : Disorder N P => |Real.log (partition N β (field c D))/(N : ℝ)-F|) :=
    continuous_abs.measurable.comp hlog
  have hmass : Measurable (fun D : Disorder N P => (gibbsLaw N β (field c D)).real
      (goodReferenceSet (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w) D)ᶜ) := by
    simpa only [goodReferenceSet_compl_mass_eq hN c β] using hm
  exact (measurableSet_le hpressure measurable_const).inter (measurableSet_le hmass measurable_const)

/-- A Borel disorder event with an actual Borel spherical good set and the
three manuscript mass inequalities. Its failure bound retains precisely the
two remaining quantitative inputs: pressure and the joint partition tests. -/
theorem goodCapCoreCollarEvent_failure_le {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w : ℝ) {a : ℝ} (ha : 0 < a) :
    (disorderLaw N P).real (goodCapCoreCollarEvent c β F J G δ q₁ q₂ q w a)ᶜ ≤
      (disorderLaw N P).real {D | δ < |Real.log (partition N β (field c D))/(N : ℝ)-F|}+
        (gibbsReferenceLaw (N := N) c β).real (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w)/a := by
  have hE := capCoreCollarBadEvent_measurable (N := N) c β F J G δ q₁ q₂ q w
  have hm := goodReferenceSet_failure_le hN c β hE ha
  have heq : (goodCapCoreCollarEvent c β F J G δ q₁ q₂ q w a)ᶜ =
      {D : Disorder N P | δ < |Real.log (partition N β (field c D))/(N : ℝ)-F|} ∪
        {D | a < (gibbsLaw N β (field c D)).real
          (goodReferenceSet (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w) D)ᶜ} := by
    ext D
    simp only [goodCapCoreCollarEvent,mem_compl_iff,mem_ofPred_eq,mem_union,not_and_or,not_le]
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add le_rfl hm)

theorem goodCapCoreCollarEvent_has_good_set {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w a : ℝ) {D : Disorder N P}
    (hD : D ∈ goodCapCoreCollarEvent c β F J G δ q₁ q₂ q w a) :
    ∃ S : Set (Vector N), MeasurableSet S ∧ S ⊆ {u | ‖u‖^2=(N : ℝ)} ∧
      (gibbsLaw N β (field c D)).real Sᶜ ≤ a ∧ ∀ u ∈ S,
        (gibbsLaw N β (field c D)).real (cap u q₁) ≤ Real.exp (-(N : ℝ)*(J-2*δ)) ∧
          Real.exp (-(N : ℝ)*(J+2*δ)) ≤ (gibbsLaw N β (field c D)).real (coreBand u q w) ∧
          (gibbsLaw N β (field c D)).real (collar u q₁ q₂) ≤ Real.exp (-(N : ℝ)*(J+G-2*δ)) := by
  refine ⟨goodReferenceSet (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w) D,
    goodReferenceSet_measurable (capCoreCollarBadEvent_measurable c β F J G δ q₁ q₂ q w) D,
    goodReferenceSet_subset_sphere _ D,hD.2,?_⟩
  intro u hu
  exact goodReferenceSet_cap_core_collar hN c β F J G δ q₁ q₂ q w D hD.1 hu

end
end SlowEquilibration.SphericalModel
