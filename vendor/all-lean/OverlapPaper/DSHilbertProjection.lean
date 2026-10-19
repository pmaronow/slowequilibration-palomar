module

public import OverlapPaper.DovbyshSudakov

@[expose] public section

/-! The actual directing measure on the whole Hilbert space. The
conditional iid samples have unit-ball support almost surely, and their
off-diagonal Gram law is the given real overlap law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 700000

def hilbertUnitSet : Set DSHilbert := {v | ‖v‖≤1}

theorem measurableSet_hilbertUnitSet : MeasurableSet hilbertUnitSet :=
  measurableSet_le measurable_id.norm measurable_const

def hilbertUnitDirectingLaw (Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall)) :
    ProbabilityMeasure (ProbabilityMeasure DSHilbert) :=
  Λ.map (probabilityPushMap (Subtype.val : DSNormBall→DSHilbert))

theorem hilbertUnitDirectingLaw_supported (Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall)) :
    ∀ᵐ (μ : ProbabilityMeasure DSHilbert) ∂(hilbertUnitDirectingLaw Λ : Measure (ProbabilityMeasure DSHilbert)),
      (μ : Measure DSHilbert) hilbertUnitSet=1 := by
  have hm : Measurable (fun μ : ProbabilityMeasure DSHilbert =>
      (μ : Measure DSHilbert) hilbertUnitSet) :=
    (Measure.measurable_coe measurableSet_hilbertUnitSet).comp measurable_subtype_coe
  change ∀ᵐ (μ : ProbabilityMeasure DSHilbert) ∂(Λ : Measure (ProbabilityMeasure DSNormBall)).map
    (probabilityPushMap (Subtype.val : DSNormBall→DSHilbert)),(μ : Measure DSHilbert) hilbertUnitSet=1
  apply (ae_map_iff (measurable_probabilityPushMap _ measurable_subtype_coe).aemeasurable
    (measurableSet_eq_fun hm measurable_const)).mpr
  apply Eventually.of_forall
  intro μ
  change (μ : Measure DSNormBall).map (Subtype.val : DSNormBall→DSHilbert) hilbertUnitSet=1
  rw [Measure.map_apply measurable_subtype_coe measurableSet_hilbertUnitSet]
  have he : (Subtype.val : DSNormBall→DSHilbert) ⁻¹' hilbertUnitSet=univ := by
    ext v
    exact iff_true_intro v.2
  rw [he,measure_univ]

theorem hilbertUnitDirectingLaw_ae_norm_le_one (Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall)) :
    ∀ᵐ (μ : ProbabilityMeasure DSHilbert) ∂(hilbertUnitDirectingLaw Λ : Measure (ProbabilityMeasure DSHilbert)),
      ∀ᵐ x ∂(μ : Measure DSHilbert), ‖x‖≤1 := by
  filter_upwards [hilbertUnitDirectingLaw_supported Λ] with μ hμ
  exact (mem_ae_iff_prob_eq_one measurableSet_hilbertUnitSet).mpr hμ

def realOverlapArray (R : OverlapArray) : ReplicaPair→ℝ := fun ij => (R ij).1

theorem continuous_realOverlapArray : Continuous realOverlapArray :=
  continuous_pi (fun ij => continuous_subtype_val.comp (continuous_apply ij))

def hilbertOffDiagonalArray (v : ℕ→DSHilbert) : ReplicaPair→ℝ := fun ij =>
  inner ℝ (v ij.1.1) (v ij.1.2)

theorem measurable_hilbertOffDiagonalArray : Measurable hilbertOffDiagonalArray :=
  Measurable.of_eval (fun ij => (measurable_pi_apply ij.1.1).inner (measurable_pi_apply ij.1.2))

def hilbertOffDiagonalSamplingProbability (Λ : ProbabilityMeasure (ProbabilityMeasure DSHilbert)) :
    ProbabilityMeasure (ReplicaPair→ℝ) :=
  ⟨(randomSamplingLaw (Λ : Measure (ProbabilityMeasure DSHilbert))).map
    (fun p => hilbertOffDiagonalArray p.2),inferInstance⟩

theorem hilbertOffDiagonalSamplingProbability_unitLaw (Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall)) :
    hilbertOffDiagonalSamplingProbability (hilbertUnitDirectingLaw Λ)=
      (ballOverlapSamplingProbability Λ).map realOverlapArray := by
  apply ProbabilityMeasure.toMeasure_injective
  change (randomSamplingLaw ((Λ : Measure (ProbabilityMeasure DSNormBall)).map
    (probabilityPushMap (Subtype.val : DSNormBall→DSHilbert)))).map
      (fun p => hilbertOffDiagonalArray p.2)=
      ((randomSamplingLaw (Λ : Measure (ProbabilityMeasure DSNormBall))).map
        (fun p => ballOverlapArray p.2)).map realOverlapArray
  rw [←randomSamplingLaw_map (Λ : Measure (ProbabilityMeasure DSNormBall))
    (Subtype.val : DSNormBall→DSHilbert) measurable_subtype_coe]
  rw [Measure.map_map
    (g := fun p : ProbabilityMeasure DSHilbert×(ℕ→DSHilbert) => hilbertOffDiagonalArray p.2)
    (f := Prod.map (probabilityPushMap (Subtype.val : DSNormBall→DSHilbert))
      (fun v : ℕ→DSNormBall => fun i : ℕ => (v i).1))
    (measurable_hilbertOffDiagonalArray.comp measurable_snd)
    ((measurable_probabilityPushMap _ measurable_subtype_coe).prodMap
      (Measurable.of_eval (fun i : ℕ => measurable_subtype_coe.comp (measurable_pi_apply i)))),
    Measure.map_map (f := fun p : ProbabilityMeasure DSNormBall×(ℕ→DSNormBall) => ballOverlapArray p.2)
      continuous_realOverlapArray.measurable (measurable_ballOverlapArray.comp measurable_snd)]
  rfl

theorem dovbysh_sudakov_hilbert (ν : ProbabilityMeasure OverlapArray)
    (hG : (ν : Measure OverlapArray) GramArrays=1) (hν : WeaklyExchangeableOverlapLaw ν) :
    ∃Λ : ProbabilityMeasure (ProbabilityMeasure DSHilbert),
      hilbertOffDiagonalSamplingProbability Λ=ν.map realOverlapArray ∧
      ∀ᵐ (μ : ProbabilityMeasure DSHilbert) ∂(Λ : Measure (ProbabilityMeasure DSHilbert)),
        ∀ᵐ x ∂(μ : Measure DSHilbert), ‖x‖≤1 := by
  obtain ⟨Λ,hΛ⟩ := dovbysh_sudakov ν hG hν
  refine ⟨hilbertUnitDirectingLaw Λ,?_,hilbertUnitDirectingLaw_ae_norm_le_one Λ⟩
  rw [hilbertOffDiagonalSamplingProbability_unitLaw,hΛ]

end OverlapPaper
