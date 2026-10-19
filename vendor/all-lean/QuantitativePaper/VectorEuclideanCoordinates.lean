module
public import QuantitativePaper.VectorGaussianCoordinates
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-! All disorder and field increments as a single standard Euclidean Gaussian.
Only the independent completion coordinate is rescaled by `sqrt(1/2)`. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace QuantitativePaper

abbrev VectorGaussianIndex (n k : ℕ) := Option (Edge n) ⊕ (Fin (k+2) × Fin n)
abbrev VectorGaussianSpace (n k : ℕ) := EuclideanSpace ℝ (VectorGaussianIndex n k)

def flatCompletionCoordinates (n : ℕ) (z : Option (Edge n) → ℝ) : Couplings n × ℝ :=
  (fun e => z (some e),Real.sqrt (1/2 : ℝ)*z none)

theorem measurable_flatCompletionCoordinates (n : ℕ) : Measurable (flatCompletionCoordinates n) := by
  unfold flatCompletionCoordinates
  exact (Measurable.of_eval fun e => measurable_pi_apply _).prodMk
    ((measurable_pi_apply none).const_mul _)

theorem flatCompletionCoordinates_map (n : ℕ) :
    (Measure.pi (fun _ : Option (Edge n) => gaussianReal 0 1)).map
      (flatCompletionCoordinates n) = completionLaw n := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Edge n) => ℝ)
  have he : (Measure.pi (fun _ : Option (Edge n) => gaussianReal 0 1)).map e =
      (couplingLaw n).prod (gaussianReal 0 1) := by
    rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
    exact (Measure.pi_map_piOptionEquivProd (fun _ : Option (Edge n) => gaussianReal 0 1)).symm
  have hs : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (1/2 : ℝ)*x) =
      gaussianReal 0 (1/2) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)]
  have hf : flatCompletionCoordinates n =
      (Prod.map id (fun x : ℝ => Real.sqrt (1/2 : ℝ)*x)) ∘ e := by
    funext z
    simp [flatCompletionCoordinates,e,MeasurableEquiv.piOptionEquivProd]
    rfl
  rw [hf,←Measure.map_map (measurable_id.prodMap (by fun_prop)) e.measurable,he,
    ←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id,hs]
  rfl

def flatFieldCoordinates (n k : ℕ) (z : Fin (k+2) × Fin n → ℝ) : Fin (k+2) → Field n :=
  fun j => WithLp.toLp 2 (fun i => z (j,i))

theorem measurable_flatFieldCoordinates (n k : ℕ) : Measurable (flatFieldCoordinates n k) := by
  unfold flatFieldCoordinates
  apply Measurable.of_eval
  intro j
  fun_prop

theorem flatFieldCoordinates_map (n k : ℕ) :
    (Measure.pi (fun _ : Fin (k+2) × Fin n => gaussianReal 0 1)).map (flatFieldCoordinates n k) =
      Measure.pi (fun _ : Fin (k+2) => fieldGaussian n) := by
  have hc : (Measure.pi (fun _ : Fin (k+2) × Fin n => gaussianReal 0 1)).map
      (MeasurableEquiv.curry (Fin (k+2)) (Fin n) ℝ) =
      Measure.pi (fun _ : Fin (k+2) => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun _ : Fin (k+2) => fun _ : Fin n => gaussianReal 0 1)
  have hf : flatFieldCoordinates n k =
      (fun z : Fin (k+2) → (Fin n → ℝ) => fun j => WithLp.toLp 2 (z j)) ∘
        MeasurableEquiv.curry (Fin (k+2)) (Fin n) ℝ := rfl
  rw [hf,←Measure.map_map (by fun_prop) (MeasurableEquiv.curry _ _ _).measurable,hc,
    Measure.pi_map_pi (fun _ => by fun_prop)]
  rfl

def vectorRawGaussianCoordinates (n k : ℕ) (z : VectorGaussianIndex n k → ℝ) :
    VectorGaussianCoordinates n k :=
  (flatCompletionCoordinates n (fun i => z (.inl i)),
    flatFieldCoordinates n k (fun i => z (.inr i)))

theorem measurable_vectorRawGaussianCoordinates (n k : ℕ) :
    Measurable (vectorRawGaussianCoordinates n k) :=
  ((measurable_flatCompletionCoordinates n).comp (Measurable.of_eval fun i => measurable_pi_apply _)).prodMk
    ((measurable_flatFieldCoordinates n k).comp (Measurable.of_eval fun i => measurable_pi_apply _))

theorem vectorRawGaussianCoordinates_map (n k : ℕ) :
    (Measure.pi (fun _ : VectorGaussianIndex n k => gaussianReal 0 1)).map
      (vectorRawGaussianCoordinates n k) = vectorGaussianCoordinateLaw n k := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : VectorGaussianIndex n k => ℝ)
  have he := (measurePreserving_sumPiEquivProdPi
    (fun _ : VectorGaussianIndex n k => gaussianReal 0 1)).map_eq
  have hf : vectorRawGaussianCoordinates n k =
      (Prod.map (flatCompletionCoordinates n) (flatFieldCoordinates n k)) ∘ e := rfl
  rw [hf,←Measure.map_map ((measurable_flatCompletionCoordinates n).prodMap
    (measurable_flatFieldCoordinates n k)) e.measurable,he,←Measure.map_prod_map _ _
      (measurable_flatCompletionCoordinates n) (measurable_flatFieldCoordinates n k),
    flatCompletionCoordinates_map,flatFieldCoordinates_map]
  rfl

def vectorEuclideanCoordinates (n k : ℕ) (z : VectorGaussianSpace n k) :
    VectorGaussianCoordinates n k := vectorRawGaussianCoordinates n k (WithLp.ofLp z)

theorem measurable_vectorEuclideanCoordinates (n k : ℕ) :
    Measurable (vectorEuclideanCoordinates n k) :=
  (measurable_vectorRawGaussianCoordinates n k).comp (by fun_prop)

theorem vectorEuclideanCoordinates_map (n k : ℕ) :
    (SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n k)).map
      (vectorEuclideanCoordinates n k) = vectorGaussianCoordinateLaw n k := by
  rw [SYK.standardGaussianMeasureOnEuclidean,Measure.map_map
    (measurable_vectorEuclideanCoordinates n k) (by fun_prop)]
  exact vectorRawGaussianCoordinates_map n k

def vectorEuclideanJointMap {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ)
    (p : VectorGaussianSpace n k × Configuration n) :
    FourPapersCommon.FiniteHistory (VectorState n) (k+2) × Configuration n :=
  vectorCoordinateJointMap s β t (vectorEuclideanCoordinates n k p.1,p.2)

theorem measurable_vectorEuclideanJointMap {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ) :
    Measurable (vectorEuclideanJointMap (n := n) s β t) :=
  (measurable_vectorCoordinateJointMap s β t).comp
    ((measurable_vectorEuclideanCoordinates n k).prodMap measurable_id)

def vectorEuclideanDensity {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t a : ℝ)
    (p : VectorGaussianSpace n k × Configuration n) : ℝ≥0∞ :=
  vectorNormalizedDensity s β t a (vectorEuclideanJointMap s β t p)

theorem measurable_vectorEuclideanDensity {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t a : ℝ) :
    Measurable (vectorEuclideanDensity (n := n) s β t a) :=
  ((measurable_vectorFullHistoryDensity s β t a).comp measurable_fst |>.mul
    (measurable_vectorHistoryTerminalWeight s β t)).comp (measurable_vectorEuclideanJointMap s β t)

def vectorEuclideanJointLaw {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t a : ℝ) :
    Measure (VectorGaussianSpace n k × Configuration n) :=
  ((SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n k)).prod
    (Measure.count : Measure (Configuration n))).withDensity (vectorEuclideanDensity s β t a)

theorem vectorEuclideanJointMap_base_map {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ) :
    ((SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n k)).prod
      (Measure.count : Measure (Configuration n))).map (vectorEuclideanJointMap s β t) =
    (vectorBaseFieldHistoryLaw (n := n) s β t).prod (Measure.count : Measure (Configuration n)) := by
  have hh : Measurable (vectorCoordinateHistory s β t ∘ vectorEuclideanCoordinates n k) :=
    (measurable_vectorCoordinateHistory s β t).comp (measurable_vectorEuclideanCoordinates n k)
  change ((SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n k)).prod
      (Measure.count : Measure (Configuration n))).map
    (Prod.map (vectorCoordinateHistory s β t ∘ vectorEuclideanCoordinates n k) id) = _
  rw [←Measure.map_prod_map _ _ hh measurable_id,←Measure.map_map
    (measurable_vectorCoordinateHistory s β t) (measurable_vectorEuclideanCoordinates n k),
    vectorEuclideanCoordinates_map,vectorCoordinateHistory_map,Measure.map_id]

theorem vectorEuclideanJointLaw_map {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t a : ℝ) :
    (vectorEuclideanJointLaw (n := n) s β t a).map (vectorEuclideanJointMap s β t) =
      vectorJointLaw s β t a := by
  unfold vectorEuclideanJointLaw
  change (((SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n k)).prod
      (Measure.count : Measure (Configuration n))).withDensity
    (fun p => vectorNormalizedDensity s β t a (vectorEuclideanJointMap s β t p))).map _ = _
  rw [FourPapersCommon.map_withDensity_pullback _ _ (measurable_vectorEuclideanJointMap s β t)
    (vectorNormalizedDensity s β t a) ((measurable_vectorFullHistoryDensity s β t a).comp measurable_fst |>.mul
      (measurable_vectorHistoryTerminalWeight s β t)),vectorEuclideanJointMap_base_map,
    vectorJointLaw_eq_normalizedDensity,Measure.compProd_const]

theorem vectorEuclideanJointLaw_probability {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β t a : ℝ) :
    IsProbabilityMeasure (vectorEuclideanJointLaw (n := n) s β t a) := by
  constructor
  have hp := vectorJointLaw_probability (n := n) s β t a
  have hm := congrArg (fun μ : Measure (FourPapersCommon.FiniteHistory (VectorState n) (k+2) × Configuration n) =>
    μ univ) (vectorEuclideanJointLaw_map (n := n) s β t a)
  rw [Measure.map_apply (measurable_vectorEuclideanJointMap s β t) MeasurableSet.univ,preimage_univ] at hm
  exact hm.trans hp.measure_univ

end QuantitativePaper
