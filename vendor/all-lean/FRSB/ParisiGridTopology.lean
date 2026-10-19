module
public import FRSB.ParisiMeasureTopology
public import Paper.ParisiCDFGrid

@[expose] public section

/-! Actual weak convergence of the already constructed equally spaced upward
Parisi quantizations. This complements their checked CDF-distance bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FRSB
open Paper

theorem tendsto_parisiGridMeasure (μ : ParisiMeasure) :
    Tendsto (parisiGridMeasure μ) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have he (n : ℕ) : (∫ q, f q ∂(parisiGridMeasure μ n : Measure Overlap)) =
      ∫ q, f (parisiGridRound n q) ∂(μ : Measure Overlap) := by
    unfold parisiGridMeasure
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map_of_stronglyMeasurable (measurable_parisiGridRound n)
      f.continuous.measurable.stronglyMeasurable
  simp_rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
  · exact .of_forall fun n => (f.continuous.measurable.comp
      (measurable_parisiGridRound n)).aestronglyMeasurable
  · exact .of_forall fun _ => .of_forall fun _ => f.norm_coe_le_norm _
  · exact integrable_const _
  · exact .of_forall fun q => f.continuous.continuousAt.tendsto.comp
      (tendsto_parisiGridRound q)

end FRSB
