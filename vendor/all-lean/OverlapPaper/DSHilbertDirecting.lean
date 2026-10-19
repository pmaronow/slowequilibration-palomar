module

public import OverlapPaper.DSInfiniteCoordinateLaw
public import OverlapPaper.DSConditionalSamplingTransport

@[expose] public section

/-! Actual random directing measures on the Hilbert unit ball and their
literal conditional iid Gram array representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 700000

def hilbertBallDirectingMap (μ : DSDirectingSpace) : ProbabilityMeasure DSNormBall :=
  probabilityPushMap coordinatesUnitHilbert (toCoordinateProbability μ)

theorem measurable_hilbertBallDirectingMap : Measurable hilbertBallDirectingMap :=
  (measurable_probabilityPushMap _ measurable_coordinatesUnitHilbert).comp measurable_toCoordinateProbability

def hilbertBallDirectingLaw (ρ : ProbabilityMeasure DSDirectingSpace) : Measure (ProbabilityMeasure DSNormBall) :=
  (ρ : Measure DSDirectingSpace).map hilbertBallDirectingMap

instance hilbertBallDirectingLaw_probability (ρ : ProbabilityMeasure DSDirectingSpace) :
    IsProbabilityMeasure (hilbertBallDirectingLaw ρ) := by
  unfold hilbertBallDirectingLaw
  infer_instance

theorem hilbertBallSampling_transport (ρ : ProbabilityMeasure DSDirectingSpace) :
    (coordinateInfiniteSamplingLaw ρ).map
      (Prod.map hilbertBallDirectingMap (fun v i => coordinatesUnitHilbert (v i)))=
      randomSamplingLaw (hilbertBallDirectingLaw ρ) := by
  apply compProd_transport (ρ : Measure DSDirectingSpace) coordinateInfiniteSamplingKernel
    (iidSamplingKernel DSNormBall) hilbertBallDirectingMap measurable_hilbertBallDirectingMap _
    (Measurable.of_eval (fun i => measurable_coordinatesUnitHilbert.comp (measurable_pi_apply i)))
  intro μ
  change (Measure.infinitePi (fun _ : ℕ => (toCoordinateProbability μ : Measure DSCoordinateBall))).map
    (fun v i => coordinatesUnitHilbert (v i))=
      Measure.infinitePi (fun _ : ℕ =>
        (probabilityPushMap coordinatesUnitHilbert (toCoordinateProbability μ) : Measure DSNormBall))
  exact iidSamplingLaw_map _ _ measurable_coordinatesUnitHilbert

theorem abs_ball_inner_le_one (v w : DSNormBall) : |inner ℝ v.1 w.1|≤1 := by
  rw [←Real.norm_eq_abs]
  apply (norm_inner_le_norm _ _).trans
  nlinarith [v.2,w.2,norm_nonneg v.1,norm_nonneg w.1]

def ballOverlapArray (v : ℕ→DSNormBall) : OverlapArray :=
  fun ij => ⟨inner ℝ (v ij.1.1).1 (v ij.1.2).1,abs_le.mp (abs_ball_inner_le_one _ _)⟩

theorem measurable_ballOverlapArray : Measurable ballOverlapArray := by
  apply Measurable.of_eval
  intro ij
  exact (((measurable_subtype_coe.comp (measurable_pi_apply ij.1.1)).inner
    (measurable_subtype_coe.comp (measurable_pi_apply ij.1.2)))).subtype_mk

theorem ballOverlapArray_coordinates (v : ℕ→DSCoordinateBall) :
    ballOverlapArray (fun i => coordinatesUnitHilbert (v i))=coordinateOverlapArray v := rfl

def ballOverlapSamplingProbability (Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall)) :
    ProbabilityMeasure OverlapArray :=
  ⟨(randomSamplingLaw (Λ : Measure (ProbabilityMeasure DSNormBall))).map (fun p => ballOverlapArray p.2),inferInstance⟩

theorem ballOverlapSamplingProbability_hilbertLaw (ρ : ProbabilityMeasure DSDirectingSpace) :
    ballOverlapSamplingProbability ⟨hilbertBallDirectingLaw ρ,inferInstance⟩=
      coordinateOverlapSamplingProbability ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  change (randomSamplingLaw (hilbertBallDirectingLaw ρ)).map (fun p => ballOverlapArray p.2)=
    (coordinateInfiniteSamplingLaw ρ).map (fun p => coordinateOverlapArray p.2)
  rw [←hilbertBallSampling_transport ρ,Measure.map_map
    (g := fun p : ProbabilityMeasure DSNormBall×(ℕ→DSNormBall) => ballOverlapArray p.2)
    (f := Prod.map hilbertBallDirectingMap
      (fun v : ℕ→DSCoordinateBall => fun i : ℕ => coordinatesUnitHilbert (v i)))
    (measurable_ballOverlapArray.comp measurable_snd)
    (measurable_hilbertBallDirectingMap.prodMap
      (Measurable.of_eval (fun i : ℕ => measurable_coordinatesUnitHilbert.comp
        (measurable_pi_apply (X := fun _ : ℕ => DSCoordinateBall) i))))]
  rfl

theorem exists_hilbert_ball_directing_representation (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val)) :
    ∃Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall),
      ballOverlapSamplingProbability Λ=ν.map Subtype.val := by
  obtain ⟨ρ,hρ⟩ := exists_coordinate_directing_representation ν hν
  exact ⟨⟨hilbertBallDirectingLaw ρ,inferInstance⟩,
    (ballOverlapSamplingProbability_hilbertLaw ρ).trans hρ⟩

end OverlapPaper
