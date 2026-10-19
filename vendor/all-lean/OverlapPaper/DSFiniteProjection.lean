module

public import OverlapPaper.DSFiniteIIDWeak
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-! Literal first-k marginals of the actual infinite iid law. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace OverlapPaper
set_option maxHeartbeats 400000

variable {E : Type*} [MeasurableSpace E]

def firstFiniteSamples (k : ℕ) (a : ℕ→E) : Fin k→E := fun i => a i.val

theorem measurable_firstFiniteSamples (k : ℕ) : Measurable (firstFiniteSamples (E := E) k) :=
  Measurable.of_eval (fun i => measurable_pi_apply i.val)

theorem infiniteIID_firstFiniteSamples (k : ℕ) (μ : ProbabilityMeasure E) :
    (Measure.infinitePi (fun _ : ℕ => (μ : Measure E))).map (firstFiniteSamples k)=
      (finiteIIDProbability k μ : Measure (Fin k→E)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_firstFiniteSamples k) (MeasurableSet.univ_pi hs)]
  let S : ℕ→Set E := fun i => if h : i<k then s ⟨i,h⟩ else univ
  have he : firstFiniteSamples k ⁻¹' univ.pi s=(Finset.range k : Set ℕ).pi S := by
    ext a
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_const,Finset.mem_coe,Finset.mem_range,
      firstFiniteSamples]
    constructor
    · intro h i hi
      simpa only [S,dite_eq_left hi] using h ⟨i,hi⟩
    · intro h i
      simpa only [S,dite_eq_left i.isLt] using h i.val i.isLt
  rw [he,Measure.infinitePi_pi]
  · rw [←Fin.prod_univ_eq_prod_range (fun i : ℕ => (μ : Measure E) (S i)) k]
    apply Finset.prod_congr rfl
    intro i _
    simp only [S,dite_eq_left i.isLt]
  · intro i hi
    have hik : i<k := Finset.mem_range.mp hi
    simpa only [S,dite_eq_left hik] using hs ⟨i,hik⟩

theorem integral_firstFiniteSamples_infiniteIID (k : ℕ) (μ : ProbabilityMeasure E)
    (f : (Fin k→E)→ℝ) (hf : Measurable f) :
    ∫a,f (firstFiniteSamples k a) ∂Measure.infinitePi (fun _ : ℕ => (μ : Measure E))=
      ∫a,f a ∂(finiteIIDProbability k μ : Measure (Fin k→E)) := by
  rw [←infiniteIID_firstFiniteSamples k μ]
  exact (integral_map (measurable_firstFiniteSamples k).aemeasurable hf.aestronglyMeasurable).symm

end OverlapPaper
