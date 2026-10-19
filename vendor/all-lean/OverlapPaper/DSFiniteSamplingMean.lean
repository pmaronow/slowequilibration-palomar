module

public import OverlapPaper.DSFiniteIIDWeak
public import OverlapPaper.DSDirectingTopology
public import OverlapPaper.DSSamplingCollision

@[expose] public section

/-! Actual finite iid sampling means are continuous functions of a directing
measure, and finite empirical sampling is exactly iid uniform index sampling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 400000

section
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

theorem finiteIIDProbability_map (k : ℕ) (μ : ProbabilityMeasure E) (f : E→F) (hf : Measurable f) :
    finiteIIDProbability k (μ.map f)=(finiteIIDProbability k μ).map (fun a i => f (a i)) := by
  apply Subtype.ext
  exact (Measure.pi_map_pi (fun _ : Fin k => hf.aemeasurable)).symm

theorem finiteIIDProbability_empirical {n k : ℕ} (hn : 0<n) (v : Fin n→E) :
    (finiteIIDProbability k (finiteEmpiricalProbability hn v) : Measure (Fin k→E))=
      (iidUniformSamplingLaw n k hn).map (fun a i => v (a i)) := by
  rw [finiteEmpiricalProbability,finiteIIDProbability_map k _ v (measurable_of_countable v)]
  rfl

end

def finiteCoordinateSamplingMean (k : ℕ) (f : C((Fin k→DSCoordinateBall),ℝ))
    (ρ : DSDirectingSpace) : ℝ := ∫v,f v ∂(finiteIIDProbability k (toCoordinateProbability ρ) : Measure _)

theorem continuous_finiteCoordinateSamplingMean (k : ℕ) (f : C((Fin k→DSCoordinateBall),ℝ)) :
    Continuous (finiteCoordinateSamplingMean k f) :=
  (ProbabilityMeasure.continuous_integral_continuousMap f).comp
    ((continuous_finiteIIDProbability k).comp continuous_toCoordinateProbability)

theorem tendsto_integral_finiteCoordinateSamplingMean (k : ℕ) (f : C((Fin k→DSCoordinateBall),ℝ))
    {ρ : ProbabilityMeasure DSDirectingSpace} {ρn : ℕ→ProbabilityMeasure DSDirectingSpace}
    (hlim : Tendsto ρn atTop (𝓝 ρ)) :
    Tendsto (fun n => ∫μ,finiteCoordinateSamplingMean k f μ ∂(ρn n : Measure DSDirectingSpace))
      atTop (𝓝 (∫μ,finiteCoordinateSamplingMean k f μ ∂(ρ : Measure DSDirectingSpace))) := by
  let g : C(DSDirectingSpace,ℝ) := ⟨finiteCoordinateSamplingMean k f,continuous_finiteCoordinateSamplingMean k f⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (BoundedContinuousFunction.mkOfCompact g)

end OverlapPaper
