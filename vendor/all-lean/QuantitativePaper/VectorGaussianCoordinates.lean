module
public import QuantitativePaper.VectorNormalizedDensity
public import FourPapersCommon.IndependentHistory

@[expose] public section

/-! Genuine independent Gaussian coordinates for the entire unweighted
finite vector path, and the pullback of the actual normalized joint density.
The retained disorder is sampled once. Degenerate field variances require
no inverse coordinate map. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

abbrev VectorGaussianCoordinates (n k : ℕ) :=
  (Couplings n × ℝ) × (Fin (k+2) → Field n)

def vectorGaussianCoordinateLaw (n k : ℕ) : Measure (VectorGaussianCoordinates n k) :=
  (completionLaw n).prod (Measure.pi (fun _ : Fin (k+2) => fieldGaussian n))

instance vectorGaussianCoordinateLaw_probability (n k : ℕ) :
    IsProbabilityMeasure (vectorGaussianCoordinateLaw n k) := by
  unfold vectorGaussianCoordinateLaw
  infer_instance

def vectorCoordinateUpdate {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (x : VectorState n) (z : Field n) : VectorState n :=
  if i ≤ k+1 then vectorStateUpdate ((1-t)*(β^2*(s.q (i+1)-s.q i))) (x,z) else x

theorem measurable_vectorCoordinateUpdate {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    Measurable (Function.uncurry (vectorCoordinateUpdate (n := n) s β t i)) := by
  unfold vectorCoordinateUpdate
  split_ifs
  · exact measurable_vectorStateUpdate _
  · exact measurable_fst

theorem vectorProfileBaseKernel_eq_coordinateUpdate {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (i : ℕ) (x : VectorState n) :
    vectorProfileBaseKernel s β t i x =
      (fieldGaussian n).map (vectorCoordinateUpdate s β t i x) := by
  unfold vectorProfileBaseKernel vectorCoordinateUpdate
  split_ifs
  · rw [vectorGaussianStateKernel_apply]
    rfl
  · simp [Kernel.id_apply]

def vectorCoordinateHistory {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorGaussianCoordinates n k) : FiniteHistory (VectorState n) (k+2) :=
  independentHistory (vectorCoordinateUpdate s β t) (k+2) ((p.1,0),p.2)

theorem measurable_vectorCoordinateHistory {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measurable (vectorCoordinateHistory (n := n) s β t) :=
  (measurable_independentHistory _ (measurable_vectorCoordinateUpdate s β t) _).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem vectorCoordinateHistory_map {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    (vectorGaussianCoordinateLaw n k).map (vectorCoordinateHistory s β t) =
      vectorBaseFieldHistoryLaw (n := n) s β t := by
  have h := independentHistory_law (vectorBaseInitialLaw n) (fieldGaussian n)
    (vectorCoordinateUpdate s β t) (measurable_vectorCoordinateUpdate s β t)
    (vectorProfileBaseKernel s β t) (vectorProfileBaseKernel_markov s β t)
    (vectorProfileBaseKernel_eq_coordinateUpdate s β t) (k+2)
  have he : (vectorBaseInitialLaw n).prod (Measure.pi (fun _ : Fin (k+2) => fieldGaussian n)) =
      (vectorGaussianCoordinateLaw n k).map (fun p => ((p.1,0),p.2)) := by
    unfold vectorBaseInitialLaw vectorGaussianCoordinateLaw
    conv_lhs => rhs;rw [←Measure.map_id (μ := Measure.pi (fun _ : Fin (k+2) => fieldGaussian n))]
    have hm : Measurable (fun p : Couplings n × ℝ => (p,(0 : Field n))) := by fun_prop
    have hi : Measurable (id : (Fin (k+2) → Field n) → (Fin (k+2) → Field n)) := measurable_id
    haveI : SFinite (Measure.pi (fun _ : Fin (k+2) => fieldGaussian n)) := inferInstance
    rw [Measure.map_prod_map (completionLaw n)
      (Measure.pi (fun _ : Fin (k+2) => fieldGaussian n)) hm hi]
    rfl
  rw [he,Measure.map_map (measurable_independentHistory _ (measurable_vectorCoordinateUpdate s β t) _)
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)] at h
  exact h

def vectorCoordinateJointMap {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorGaussianCoordinates n k × Configuration n) :
    FiniteHistory (VectorState n) (k+2) × Configuration n :=
  (vectorCoordinateHistory s β t p.1,p.2)

theorem measurable_vectorCoordinateJointMap {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measurable (vectorCoordinateJointMap (n := n) s β t) :=
  (measurable_vectorCoordinateHistory s β t).prodMap measurable_id

def vectorCoordinateDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (p : VectorGaussianCoordinates n k × Configuration n) : ℝ≥0∞ :=
  vectorNormalizedDensity s β t a (vectorCoordinateJointMap s β t p)

theorem measurable_vectorCoordinateDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measurable (vectorCoordinateDensity (n := n) s β t a) :=
  (measurable_vectorFullHistoryDensity s β t a).comp
      ((measurable_vectorCoordinateHistory s β t).comp measurable_fst) |>.mul
    ((measurable_vectorHistoryTerminalWeight s β t).comp
      (measurable_vectorCoordinateJointMap s β t))

def vectorCoordinateJointLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measure (VectorGaussianCoordinates n k × Configuration n) :=
  ((vectorGaussianCoordinateLaw n k).prod (Measure.count : Measure (Configuration n))).withDensity
    (vectorCoordinateDensity s β t a)

theorem vectorCoordinateJointLaw_map {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    (vectorCoordinateJointLaw (n := n) s β t a).map (vectorCoordinateJointMap s β t) =
      vectorJointLaw s β t a := by
  rw [vectorCoordinateJointLaw]
  have hp := map_withDensity_pullback
    ((vectorGaussianCoordinateLaw n k).prod (Measure.count : Measure (Configuration n)))
    (vectorCoordinateJointMap s β t) (measurable_vectorCoordinateJointMap s β t)
    (vectorNormalizedDensity s β t a)
    ((measurable_vectorFullHistoryDensity s β t a).comp measurable_fst |>.mul
      (measurable_vectorHistoryTerminalWeight s β t))
  change (((vectorGaussianCoordinateLaw n k).prod Measure.count).withDensity
    (fun p => vectorNormalizedDensity s β t a (vectorCoordinateJointMap s β t p))).map _ = _
  rw [hp]
  change (((vectorGaussianCoordinateLaw n k).prod Measure.count).map
      (Prod.map (vectorCoordinateHistory s β t) id)).withDensity _ = _
  rw [←Measure.map_prod_map _ _ (measurable_vectorCoordinateHistory s β t) measurable_id,
    vectorCoordinateHistory_map,Measure.map_id,vectorJointLaw_eq_normalizedDensity,
    Measure.compProd_const]

theorem vectorCoordinateJointLaw_probability {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    IsProbabilityMeasure (vectorCoordinateJointLaw (n := n) s β t a) := by
  constructor
  have hp := vectorJointLaw_probability (n := n) s β t a
  have hm := congrArg (fun μ : Measure (FiniteHistory (VectorState n) (k+2) × Configuration n) =>
    μ univ) (vectorCoordinateJointLaw_map (n := n) s β t a)
  rw [Measure.map_apply (measurable_vectorCoordinateJointMap s β t) MeasurableSet.univ,
    preimage_univ] at hm
  exact hm.trans hp.measure_univ

end QuantitativePaper
