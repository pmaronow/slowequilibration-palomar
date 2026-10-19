module

public import OverlapPaper.DSFiniteEmbedding
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

/-! Actual finite empirical probability measures, with their weak continuity
and Giry measurability proved separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000

section
variable {E : Type*} [MeasurableSpace E]

def finiteUniformProbability (n : ℕ) (hn : 0<n) : ProbabilityMeasure (Fin n) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact ⟨(PMF.uniformOfFintype (Fin n)).toMeasure,inferInstance⟩

def finiteEmpiricalProbability {n : ℕ} (hn : 0<n) (v : Fin n→E) : ProbabilityMeasure E :=
  (finiteUniformProbability n hn).map v

theorem integral_finiteEmpiricalProbability {n : ℕ} (hn : 0<n) (v : Fin n→E)
    (f : E→ℝ) (hf : Measurable f) :
    ∫ x,f x ∂(finiteEmpiricalProbability hn v : Measure E)=(n:ℝ)⁻¹*∑ i : Fin n,f (v i) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  rw [finiteEmpiricalProbability,ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_of_countable v).aemeasurable hf.aestronglyMeasurable]
  change ∫ i,f (v i) ∂(PMF.uniformOfFintype (Fin n)).toMeasure=_
  simp only [PMF.integral_eq_sum,PMF.uniformOfFintype_apply,Fintype.card_fin,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,Finset.mul_sum]

end

section
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

theorem continuous_finiteEmpiricalProbability {n : ℕ} (hn : 0<n) :
    Continuous (finiteEmpiricalProbability (E := E) hn) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_finiteEmpiricalProbability hn _ f f.continuous.measurable]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  exact f.continuous.comp (continuous_apply i)

end

section
variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]

theorem measurable_finiteEmpiricalProbability {n : ℕ} (hn : 0<n) (v : X→Fin n→E)
    (hv : ∀ i,Measurable (fun x => v x i)) :
    Measurable (fun x => finiteEmpiricalProbability hn (v x)) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun x => (finiteUniformProbability n hn : Measure (Fin n)).map (v x) s)
  simp_rw [Measure.map_apply (measurable_of_countable _) hs]
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  change Measurable (fun x => (PMF.uniformOfFintype (Fin n)).toMeasure ((v x) ⁻¹' s))
  simp_rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (MeasurableSet.preimage hs (measurable_of_countable _)),
    PMF.toOuterMeasure_apply]
  apply Measurable.tsum
  intro i
  exact Measurable.ite ((hv i) hs) measurable_const measurable_const

end
end OverlapPaper
