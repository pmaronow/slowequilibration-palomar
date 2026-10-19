module

public import OverlapPaper.DSFiniteEmpirical
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! A compact Borel model for random directing measures. Its weak topology
is retained explicitly, and the map to the actual Giry probability space is
proved measurable by the open-set Portmanteau inequality. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
namespace OverlapPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

structure DSDirectingSpace where
  probability : ProbabilityMeasure DSCoordinateBall

instance : TopologicalSpace DSDirectingSpace := TopologicalSpace.induced DSDirectingSpace.probability inferInstance
instance : MeasurableSpace DSDirectingSpace := borel DSDirectingSpace
instance : BorelSpace DSDirectingSpace := ⟨rfl⟩

def directingHomeomorph : DSDirectingSpace ≃ₜ ProbabilityMeasure DSCoordinateBall where
  toFun := DSDirectingSpace.probability
  invFun := DSDirectingSpace.mk
  left_inv := fun ρ => by cases ρ; rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance : CompactSpace DSDirectingSpace := directingHomeomorph.symm.compactSpace
instance : MetrizableSpace DSDirectingSpace := directingHomeomorph.isEmbedding.metrizableSpace
instance : T2Space DSDirectingSpace := directingHomeomorph.isEmbedding.t2Space

/-- This map sends the weak Borel model to the actual Giry probability space. -/
def toCoordinateProbability (ρ : DSDirectingSpace) : ProbabilityMeasure DSCoordinateBall := ρ.probability

theorem continuous_toCoordinateProbability : Continuous toCoordinateProbability := directingHomeomorph.continuous

theorem measurable_toCoordinateProbability : Measurable toCoordinateProbability := by
  apply Measurable.subtype_mk
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (μ := fun ρ : DSDirectingSpace => (toCoordinateProbability ρ : Measure DSCoordinateBall))
    (BorelSpace.measurable_eq (α := DSCoordinateBall)) isPiSystem_isOpen
  intro s hs
  apply LowerSemicontinuous.measurable
  rw [lowerSemicontinuous_iff_le_liminf]
  intro ρ
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (continuous_toCoordinateProbability.continuousAt : Tendsto toCoordinateProbability (𝓝 ρ)
      (𝓝 (toCoordinateProbability ρ))) hs

def empiricalDirectingPoint {n : ℕ} (hn : 0<n) (v : Fin n→DSCoordinateBall) : DSDirectingSpace :=
  ⟨finiteEmpiricalProbability hn v⟩

theorem continuous_empiricalDirectingPoint {n : ℕ} (hn : 0<n) :
    Continuous (empiricalDirectingPoint hn) :=
  directingHomeomorph.symm.continuous.comp (continuous_finiteEmpiricalProbability hn)

theorem measurable_empiricalDirectingPoint {n : ℕ} (hn : 0<n) :
    Measurable (empiricalDirectingPoint hn) := (continuous_empiricalDirectingPoint hn).measurable

end OverlapPaper
