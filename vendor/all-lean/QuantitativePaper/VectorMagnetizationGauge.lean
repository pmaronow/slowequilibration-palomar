module
public import QuantitativePaper.VectorGauge
public import QuantitativePaper.VectorMagnetizationSmooth

@[expose] public section

/-! Genuine field-response covariance under the actual spin gauge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem fieldGauge_single {n : ℕ} (η : Configuration n) (i : Fin n) :
    fieldGauge η (EuclideanSpace.single i 1)=
      Paper.spinSign (η i) • EuclideanSpace.single i 1 := by
  ext l
  by_cases hl : l=i
  · subst l
    simp
  · simp [hl]

theorem vectorMagnetization_component_gauge {n k : ℕ} (s : RSBScheme k)
    (η : Configuration n) (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ)
    (x : Field n) (i : Fin n) :
    vectorMagnetization s β t (completionGauge η p) j (fieldGauge η x) i=
      Paper.spinSign (η i)*vectorMagnetization s β t p j x i := by
  have he : (fun r : ℝ => vectorRecursion s β t (completionGauge η p) j
      (fieldGauge η x+(r*Paper.spinSign (η i)) • EuclideanSpace.single i 1))=
      fun r => vectorRecursion s β t p j (x+r • EuclideanSpace.single i 1) := by
    funext r
    have hx : fieldGauge η (x+r • EuclideanSpace.single i 1)=
        fieldGauge η x+(r*Paper.spinSign (η i)) • EuclideanSpace.single i 1 := by
      rw [map_add,map_smul,fieldGauge_single,smul_smul]
    rw [←hx,vectorRecursion_gauge]
  have hi : HasDerivAt (fun r => vectorRecursion s β t (completionGauge η p) j
      (fieldGauge η x+r • EuclideanSpace.single i 1))
      (vectorMagnetization s β t (completionGauge η p) j (fieldGauge η x) i)
      (id 0*Paper.spinSign (η i)) := by
    simpa using hasDerivAt_vectorRecursion_coordinate s β t (completionGauge η p) j (fieldGauge η x) i
  have hh := hi.comp 0 ((hasDerivAt_id 0).mul_const (Paper.spinSign (η i)))
  simp only [Function.comp_def,id_eq] at hh
  rw [he] at hh
  have hd := hh.unique (hasDerivAt_vectorRecursion_coordinate s β t p j x i)
  cases hη : η i <;> simp [Paper.spinSign,hη] at hd ⊢ <;> linarith

theorem vectorMagnetization_gauge {n k : ℕ} (s : RSBScheme k)
    (η : Configuration n) (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorMagnetization s β t (completionGauge η p) j (fieldGauge η x)=
      fieldGauge η (vectorMagnetization s β t p j x) := by
  ext i
  exact vectorMagnetization_component_gauge s η β t p j x i

theorem vectorEuclideanMagnetization_gauge {n k : ℕ} (s : RSBScheme k)
    (η : Configuration n) (β t : ℝ) (i : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanMagnetization s β t i (vectorGaussianGauge η z)=
      fieldGauge η (vectorEuclideanMagnetization s β t i z) := by
  unfold vectorEuclideanMagnetization
  simp only [vectorEuclideanStateLinear_apply,vectorEuclideanHistory_gauge]
  exact vectorMagnetization_gauge _ _ _ _ _ _ _

theorem completionGauge_global_flip {n : ℕ} (p : Couplings n × ℝ) :
    completionGauge (fun _ : Fin n => false) p=p := by
  apply Prod.ext
  · funext e
    simp [completionGauge,couplingGauge,Paper.spinSign]
  · rfl

theorem vectorMagnetization_zero_field {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) :
    vectorMagnetization s β t p j 0=0 := by
  ext i
  have hh := vectorMagnetization_component_gauge s (fun _ => false) β t p j 0 i
  rw [completionGauge_global_flip,map_zero] at hh
  simp only [Paper.spinSign,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul] at hh
  change vectorMagnetization s β t p j 0 i=0
  linarith

end QuantitativePaper
