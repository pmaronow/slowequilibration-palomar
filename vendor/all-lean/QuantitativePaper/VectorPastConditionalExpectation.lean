module
public import QuantitativePaper.VectorPastPairing

@[expose] public section

/-! Literal conditional terminal-spin means given the entire actual retained
past. This is the natural finite-history filtration, not an assumed Markov law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

@[instance_reducible] def vectorPastSigma {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    MeasurableSpace (VectorGaussianSpace n k × Configuration n) :=
  MeasurableSpace.comap (fun p => vectorEuclideanPast s β t i p.1) inferInstance

theorem vectorPastSigma_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    vectorPastSigma (n := n) s β t i ≤
      (inferInstance : MeasurableSpace (VectorGaussianSpace n k × Configuration n)) :=
  ((measurable_vectorEuclideanPast s β t i).comp measurable_fst).comap_le

theorem condExp_vector_terminal_observable_past {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) (i : ℕ) (hi : i≤k+2) :
    (vectorEuclideanJointLaw s β t a)[(fun p => d p.2) | vectorPastSigma s β t i] =ᵐ[vectorEuclideanJointLaw s β t a]
      fun p => vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1) := by
  let P := vectorEuclideanJointLaw (n := n) s β t a
  let X := fun p : VectorGaussianSpace n k × Configuration n => vectorEuclideanStateLinear s β t i p.1
  let Y := fun p : VectorGaussianSpace n k × Configuration n => vectorEuclideanPast s β t i p.1
  let R := ∑σ : Configuration n,|d σ|
  letI := vectorEuclideanJointLaw_probability (n := n) s β t a
  have hX : Measurable X := (vectorEuclideanStateLinear s β t i).measurable.comp measurable_fst
  have hm : vectorPastSigma (n := n) s β t i ≤
      (inferInstance : MeasurableSpace (VectorGaussianSpace n k × Configuration n)) := vectorPastSigma_le s β t i
  have hd (σ : Configuration n) : |d σ|≤R :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hf : Integrable (fun p : VectorGaussianSpace n k × Configuration n => d p.2) P := by
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound ((measurable_of_finite d).comp measurable_snd).aestronglyMeasurable R
      (.of_forall fun p => by simpa only [Real.norm_eq_abs] using hd p.2)
  have hg : Integrable (fun p => vectorBackwardMean s β t d i (X p)) P := by
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound ((measurable_vectorBackwardMean s β t d i).comp hX).aestronglyMeasurable R
      (.of_forall fun p => by simpa only [Real.norm_eq_abs] using abs_vectorBackwardMean_le s β t d R hd i (X p))
  have hYm : Measurable[vectorPastSigma s β t i] Y := Measurable.of_comap_le le_rfl
  have hXm : Measurable[vectorPastSigma s β t i] X := by
    have hh := (measurable_pi_apply (Fin.last i)).comp hYm
    simpa only [Y,Function.comp_def,vectorEuclideanPast_last] using hh
  have hgm : AEStronglyMeasurable[vectorPastSigma s β t i]
      (fun p => vectorBackwardMean s β t d i (X p)) P :=
    ((measurable_vectorBackwardMean s β t d i).comp hXm).stronglyMeasurable.aestronglyMeasurable
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun _ _ _ => hg.integrableOn) ?_ hgm).symm
  intro E hE _
  rcases hE with ⟨S,hS,hSE⟩
  have hEg : MeasurableSet E := hm E ⟨S,hS,hSE⟩
  have hh := integral_vectorEuclideanJointLaw_terminal_past_pairing s β t a d i hi
    (S.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hS) 1
    (fun x => by by_cases hx : x∈S <;> simp [hx])
  have he1 : (fun p : VectorGaussianSpace n k × Configuration n =>
      S.indicator (fun _ => (1 : ℝ)) (Y p)*d p.2)=E.indicator (fun p => d p.2) := by
    funext p
    by_cases hp : Y p∈S
    · have hpE : p∈E := hSE ▸ hp
      simp [hp,hpE]
    · have hpE : p∉E := by rw [←hSE];exact hp
      simp [hp,hpE]
  have he2 : (fun p : VectorGaussianSpace n k × Configuration n =>
      S.indicator (fun _ => (1 : ℝ)) (Y p)*vectorBackwardMean s β t d i (X p))=
      E.indicator (fun p => vectorBackwardMean s β t d i (X p)) := by
    funext p
    by_cases hp : Y p∈S
    · have hpE : p∈E := hSE ▸ hp
      simp [hp,hpE]
    · have hpE : p∉E := by rw [←hSE];exact hp
      simp [hp,hpE]
  change (∫p,S.indicator (fun _ => (1 : ℝ)) (Y p)*d p.2 ∂P)=
    ∫p,S.indicator (fun _ => (1 : ℝ)) (Y p)*vectorBackwardMean s β t d i (X p) ∂P at hh
  rw [he1,he2,integral_indicator hEg,integral_indicator hEg] at hh
  exact hh.symm

end QuantitativePaper
