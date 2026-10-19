module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Constructions

@[expose] public section

/-! Weak continuity of genuine finite iid product probabilities. This is
proved from the actual product-measure identity, including the empty tuple. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 500000

variable {E : Type*} [MeasurableSpace E]

def finiteIIDProbability (k : ℕ) (μ : ProbabilityMeasure E) : ProbabilityMeasure (Fin k→E) :=
  ⟨Measure.pi (fun _ : Fin k => (μ : Measure E)),inferInstance⟩

theorem finiteIIDProbability_zero (μ : ProbabilityMeasure E) :
    finiteIIDProbability 0 μ=⟨Measure.dirac (isEmptyElim : Fin 0→E),inferInstance⟩ := by
  apply Subtype.ext
  exact Measure.pi_of_empty _ _

theorem finiteIIDProbability_succ (k : ℕ) (μ : ProbabilityMeasure E) :
    finiteIIDProbability (k+1) μ=(μ.prod (finiteIIDProbability k μ)).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => E) 0).symm := by
  apply Subtype.ext
  exact (MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => E) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => (μ : Measure E)) 0)).map_eq.symm

variable [TopologicalSpace E] [SecondCountableTopology E] [PseudoMetrizableSpace E] [BorelSpace E]

theorem continuous_finiteIIDProbability (k : ℕ) : Continuous (finiteIIDProbability (E := E) k) := by
  induction k with
  | zero =>
    have he : finiteIIDProbability (E := E) 0=fun _ =>
        (⟨Measure.dirac (isEmptyElim : Fin 0→E),inferInstance⟩ : ProbabilityMeasure (Fin 0→E)) := by
      funext μ
      exact finiteIIDProbability_zero μ
    rw [he]
    exact continuous_const
  | succ k ih =>
    have hc : Continuous ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => E) 0).symm :
        E×(Fin k→E)→(Fin (k+1)→E)) := by
      change Continuous (fun p : E×(Fin k→E) => Fin.insertNth (α := fun _ : Fin (k+1) => E) 0 p.1 p.2)
      exact Continuous.finInsertNth (A := fun _ : Fin (k+1) => E) 0 continuous_fst continuous_snd
    have he : finiteIIDProbability (E := E) (k+1)=fun μ =>
        (μ.prod (finiteIIDProbability k μ)).map
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => E) 0).symm := by
      funext μ
      exact finiteIIDProbability_succ k μ
    rw [he]
    exact (ProbabilityMeasure.continuous_map hc).comp
      (ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk ih))

end OverlapPaper
