module

public import OverlapPaper.DSCoordinateSamplingKernel
public import OverlapPaper.DSFiniteProjection
public import OverlapPaper.DSFiniteExchangeableSampling
public import OverlapPaper.RandomSampling
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! The actual finite conditional iid coordinate law, its pair marginals,
and the actual finite Gram observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators
namespace OverlapPaper
set_option maxHeartbeats 600000

theorem finiteIIDProbability_pair {E : Type*} [MeasurableSpace E] (μ : ProbabilityMeasure E)
    {k : ℕ} (i j : Fin k) (hij : i≠j) :
    (finiteIIDProbability k μ : Measure (Fin k→E)).map (fun a => (a i,a j))=
      (μ.prod μ : Measure (E×E)) := by
  have hind : iIndepFun (fun i : Fin k => Function.eval i)
      (Measure.pi (fun _ : Fin k => (μ : Measure E))) :=
    iIndepFun_pi (X := fun _ : Fin k => id) (fun _ => aemeasurable_id)
  change (Measure.pi (fun _ : Fin k => (μ : Measure E))).map (fun a => (a i,a j))=_
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (μ := fun _ : Fin k => (μ : Measure E)) i).map_eq,
    (measurePreserving_eval (μ := fun _ : Fin k => (μ : Measure E)) j).map_eq]
  rfl

def coordinateFiniteSamplingKernel (k : ℕ) : Kernel DSDirectingSpace (Fin k→DSCoordinateBall) :=
  ((iidSamplingKernel DSCoordinateBall).map (firstFiniteSamples k)).comap
    toCoordinateProbability measurable_toCoordinateProbability

theorem coordinateFiniteSamplingKernel_apply (k : ℕ) (ρ : DSDirectingSpace) :
    coordinateFiniteSamplingKernel k ρ=(finiteIIDProbability k (toCoordinateProbability ρ) : Measure _) := by
  rw [coordinateFiniteSamplingKernel,Kernel.comap_apply,
    Kernel.map_apply _ (measurable_firstFiniteSamples k)]
  exact infiniteIID_firstFiniteSamples k _

instance coordinateFiniteSamplingKernel_markov (k : ℕ) : IsMarkovKernel (coordinateFiniteSamplingKernel k) := by
  constructor
  intro ρ
  rw [coordinateFiniteSamplingKernel_apply]
  infer_instance

def coordinateFiniteSamplingLaw (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ) :
    Measure (DSDirectingSpace×(Fin k→DSCoordinateBall)) :=
  (ρ : Measure DSDirectingSpace) ⊗ₘ coordinateFiniteSamplingKernel k

instance coordinateFiniteSamplingLaw_probability (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ) :
    IsProbabilityMeasure (coordinateFiniteSamplingLaw ρ k) := by
  unfold coordinateFiniteSamplingLaw
  infer_instance

theorem integral_coordinateFiniteSamplingLaw (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ)
    (f : (Fin k→DSCoordinateBall)→ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀v,‖f v‖≤C) :
    ∫p,f p.2 ∂coordinateFiniteSamplingLaw ρ k=
      ∫μ,(∫v,f v ∂(finiteIIDProbability k (toCoordinateProbability μ) : Measure _))
        ∂(ρ : Measure DSDirectingSpace) := by
  have hi : Integrable (fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) => f p.2)
      (coordinateFiniteSamplingLaw ρ k) :=
    (integrable_const C).mono' (hf.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall (fun p => hb p.2))
  rw [coordinateFiniteSamplingLaw,Measure.integral_compProd hi]
  simp only [coordinateFiniteSamplingKernel_apply]

theorem integral_coordinateFiniteSamplingLaw_pair (ρ : ProbabilityMeasure DSDirectingSpace) {k : ℕ}
    (i j : Fin k) (hij : i≠j) (f : (DSCoordinateBall×DSCoordinateBall)→ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀p,‖f p‖≤C) :
    ∫p,f (p.2 i,p.2 j) ∂coordinateFiniteSamplingLaw ρ k=
      ∫p,f p.2 ∂coordinatePairSamplingLaw ρ := by
  rw [integral_coordinateFiniteSamplingLaw ρ k (fun v : Fin k→DSCoordinateBall => f (v i,v j))
    (by fun_prop) C
    (fun v => hb (v i,v j)),integral_coordinatePairSamplingLaw ρ f hf C hb]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro μ
  have hh := integral_map (μ := (finiteIIDProbability k (toCoordinateProbability μ) : Measure _))
    (φ := fun a : Fin k→DSCoordinateBall => (a i,a j))
    (f := f) ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    hf.aestronglyMeasurable
  rw [finiteIIDProbability_pair _ i j hij] at hh
  exact hh.symm

def finiteCoordinateOverlap (k : ℕ) (v : Fin k→DSCoordinateBall) : FiniteOverlapArray k :=
  fun ij => ⟨⟪coordinateVector (v ij.1.1),coordinateVector (v ij.1.2)⟫,
    abs_le.mp (abs_coordinateInner_le_one _ _)⟩

def finiteCoordinateOverlapPrefix (k M : ℕ) (v : Fin k→DSCoordinateBall) : FiniteOverlapArray k :=
  fun ij => ⟨coordinateInnerPrefix M (v ij.1.1) (v ij.1.2),
    abs_le.mp (abs_coordinateInnerPrefix_le_one M _ _)⟩

theorem measurable_finiteCoordinateOverlap (k : ℕ) : Measurable (finiteCoordinateOverlap k) := by
  apply Measurable.of_eval
  intro ij
  exact (Measurable.comp (f := fun v : Fin k→DSCoordinateBall => (v ij.1.1,v ij.1.2))
    measurable_coordinateInner
    ((measurable_pi_apply ij.1.1).prodMk (measurable_pi_apply ij.1.2))).subtype_mk

theorem continuous_finiteCoordinateOverlapPrefix (k M : ℕ) :
    Continuous (finiteCoordinateOverlapPrefix k M) := by
  apply continuous_pi
  intro ij
  exact (Continuous.comp (f := fun v : Fin k→DSCoordinateBall => (v ij.1.1,v ij.1.2))
    (continuous_coordinateInnerPrefix M)
    ((continuous_apply ij.1.1).prodMk (continuous_apply ij.1.2))).subtype_mk _

theorem finiteCoordinateOverlap_distance_le (k M : ℕ) (v : Fin k→DSCoordinateBall) :
    dist (finiteCoordinateOverlap k v) (finiteCoordinateOverlapPrefix k M v)≤
      ∑ij : FiniteReplicaPair k,|⟪coordinateVector (v ij.1.1),coordinateVector (v ij.1.2)⟫-
        coordinateInnerPrefix M (v ij.1.1) (v ij.1.2)| := by
  have hs : 0≤∑ij : FiniteReplicaPair k,|⟪coordinateVector (v ij.1.1),coordinateVector (v ij.1.2)⟫-
        coordinateInnerPrefix M (v ij.1.1) (v ij.1.2)| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (dist_pi_le_iff hs).mpr
  intro ij
  change |⟪coordinateVector (v ij.1.1),coordinateVector (v ij.1.2)⟫-
    coordinateInnerPrefix M (v ij.1.1) (v ij.1.2)|≤
    ∑ij : FiniteReplicaPair k,|⟪coordinateVector (v ij.1.1),coordinateVector (v ij.1.2)⟫-
        coordinateInnerPrefix M (v ij.1.1) (v ij.1.2)|
  exact Finset.single_le_sum (f := fun ij : FiniteReplicaPair k =>
    |⟪coordinateVector (v ij.1.1),coordinateVector (v ij.1.2)⟫-
        coordinateInnerPrefix M (v ij.1.1) (v ij.1.2)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)

end OverlapPaper
