-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.MetricSpace.Polish

@[expose] public section

/-! # Equality of genuine continuous-field laws from their finite-dimensional laws -/
namespace SlowEquilibration.ContinuousFieldLaw
noncomputable section
open MeasureTheory ProbabilityTheory Function TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K Ω Ω' V : Type*}
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace V] [CompleteSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]

/-- A fixed dense countable family really determines a continuous function. -/
def denseEvaluation (f : C(K,V)) : ℕ → V := fun n => f (denseSeq K n)

omit [CompactSpace K] [T2Space K] [CompleteSpace V] [SecondCountableTopology V] in
lemma denseEvaluation_measurable : Measurable (denseEvaluation (K := K) (V := V)) := by
  apply Measurable.of_eval
  intro n
  exact ContinuousMap.measurable_eval _

omit [CompactSpace K] [T2Space K] [CompleteSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] in
lemma denseEvaluation_injective : Injective (denseEvaluation (K := K) (V := V)) := by
  intro f g hfg
  have h : (f : K → V)=g := Continuous.ext_on (denseRange_denseSeq K) f.continuous g.continuous
    (by rintro x ⟨n,rfl⟩; exact congrFun hfg n)
  exact DFunLike.ext' h

lemma denseEvaluation_measurableEmbedding : MeasurableEmbedding (denseEvaluation (K := K) (V := V)) :=
  denseEvaluation_measurable.measurableEmbedding denseEvaluation_injective

/-- No Gaussian assumption is needed for the continuous-field transport:
genuine equality of every finite observation law determines the full Borel law. -/
theorem continuous_map_law_eq_of_finite_laws (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → C(K,V)) (Y : Ω' → C(K,V)) (hX : Measurable X) (hY : Measurable Y)
    (hfinite : ∀ I : Finset ℕ,
      P.map (fun ω (i : I) => X ω (denseSeq K (i : ℕ)))=
      Q.map (fun ω (i : I) => Y ω (denseSeq K (i : ℕ)))) :
    P.map X=Q.map Y := by
  apply (denseEvaluation_measurableEmbedding (K := K) (V := V)).map_injective
  rw [Measure.map_map denseEvaluation_measurable hX,
    Measure.map_map denseEvaluation_measurable hY]
  have hp := isProjectiveLimit_map (P := P) (denseEvaluation_measurable.comp hX).aemeasurable
  have hq := isProjectiveLimit_map (P := Q) (denseEvaluation_measurable.comp hY).aemeasurable
  have hf : (fun I : Finset ℕ => P.map (fun ω => I.restrict (denseEvaluation (X ω))))=
      fun I : Finset ℕ => Q.map (fun ω => I.restrict (denseEvaluation (Y ω))) := by
    funext I
    exact hfinite I
  change IsProjectiveLimit (P.map (denseEvaluation ∘ X))
    (fun I : Finset ℕ => P.map (fun ω => I.restrict (denseEvaluation (X ω)))) at hp
  rw [hf] at hp
  exact hp.unique hq

omit [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K]
  [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
/-- Every Borel pressure observable and every Borel event is transported by
the actual law equality, including literal log-partition statistics. -/
theorem observable_map_eq (P : Measure Ω) (Q : Measure Ω')
    (X : Ω → C(K,V)) (Y : Ω' → C(K,V)) (hX : Measurable X) (hY : Measurable Y)
    (hLaw : P.map X=Q.map Y) {T : Type*} [MeasurableSpace T]
    (F : C(K,V) → T) (hF : Measurable F) : P.map (F ∘ X)=Q.map (F ∘ Y) := by
  rw [← Measure.map_map hF hX,← Measure.map_map hF hY,hLaw]

end
end SlowEquilibration.ContinuousFieldLaw
