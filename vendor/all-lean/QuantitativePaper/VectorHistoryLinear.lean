module
public import QuantitativePaper.VectorHistoryProperties
public import QuantitativePaper.VectorEuclideanCoordinates

@[expose] public section

/-! The retained disorder/field history is an actual continuous linear map of
its independent Gaussian coordinates. Degenerate variances are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000

section Generic
variable {State Noise : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Noise] [NormedSpace ℝ Noise]

def historyInputPrefix (N : ℕ) :
    (State × (Fin (N+1) → Noise)) →L[ℝ] (State × (Fin N → Noise)) :=
  (ContinuousLinearMap.fst ℝ State (Fin (N+1) → Noise)).prod
    (ContinuousLinearMap.pi fun i : Fin N =>
      (ContinuousLinearMap.proj i.castSucc).comp (ContinuousLinearMap.snd ℝ State (Fin (N+1) → Noise)))

def independentHistoryLinear (u : ℕ → (State × Noise) →L[ℝ] State) :
    (N : ℕ) → (State × (Fin N → Noise)) →L[ℝ] (Fin (N+1) → State)
  | 0 => ContinuousLinearMap.pi fun _ => ContinuousLinearMap.fst ℝ State (Fin 0 → Noise)
  | N+1 =>
      let h := (independentHistoryLinear u N).comp (historyInputPrefix N)
      let y := (u N).comp (((ContinuousLinearMap.proj (Fin.last N)).comp h).prod
        ((ContinuousLinearMap.proj (Fin.last N)).comp (ContinuousLinearMap.snd ℝ State (Fin (N+1) → Noise))))
      ContinuousLinearMap.pi (Fin.snoc (fun i => (ContinuousLinearMap.proj i).comp h) y)

theorem independentHistoryLinear_apply (u : ℕ → (State × Noise) →L[ℝ] State)
    (N : ℕ) (p : State × (Fin N → Noise)) :
    independentHistoryLinear u N p=independentHistory (fun i x z => u i (x,z)) N p := by
  induction N with
  | zero => rfl
  | succ N ih =>
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [independentHistoryLinear,ContinuousLinearMap.pi_apply,Fin.snoc_last,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.proj_apply,
        independentHistory,Fin.snoc_last]
      rw [ih]
      rfl
    · simp only [independentHistoryLinear,ContinuousLinearMap.pi_apply,Fin.snoc_castSucc,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,independentHistory,Fin.snoc_castSucc]
      rw [ih]
      rfl
end Generic

def vectorCoordinateUpdateLinear {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    (VectorState n × Field n) →L[ℝ] VectorState n :=
  if i ≤ k+1 then
    ((ContinuousLinearMap.fst ℝ (Couplings n × ℝ) (Field n)).comp
      (ContinuousLinearMap.fst ℝ (VectorState n) (Field n))).prod
    ((ContinuousLinearMap.snd ℝ (Couplings n × ℝ) (Field n)).comp
      (ContinuousLinearMap.fst ℝ (VectorState n) (Field n))+
      Real.sqrt ((1-t)*(β^2*(s.q (i+1)-s.q i))) •
        ContinuousLinearMap.snd ℝ (VectorState n) (Field n))
  else ContinuousLinearMap.fst ℝ (VectorState n) (Field n)

theorem vectorCoordinateUpdateLinear_apply {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (z : Field n) :
    vectorCoordinateUpdateLinear s β t i (x,z)=vectorCoordinateUpdate s β t i x z := by
  unfold vectorCoordinateUpdateLinear vectorCoordinateUpdate
  split_ifs <;> rfl

def vectorCoordinateInitialLinear (n k : ℕ) :
    VectorGaussianCoordinates n k →L[ℝ] (VectorState n × (Fin (k+2) → Field n)) :=
  ((ContinuousLinearMap.fst ℝ (Couplings n × ℝ) (Fin (k+2) → Field n)).prod
    (0 : VectorGaussianCoordinates n k →L[ℝ] Field n)).prod
    (ContinuousLinearMap.snd ℝ (Couplings n × ℝ) (Fin (k+2) → Field n))

def vectorCoordinateHistoryLinear {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    VectorGaussianCoordinates n k →L[ℝ] (Fin (k+3) → VectorState n) :=
  (independentHistoryLinear (vectorCoordinateUpdateLinear s β t) (k+2)).comp
    (vectorCoordinateInitialLinear n k)

theorem vectorCoordinateHistoryLinear_apply {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorGaussianCoordinates n k) :
    vectorCoordinateHistoryLinear s β t p=vectorCoordinateHistory s β t p := by
  unfold vectorCoordinateHistoryLinear
  rw [ContinuousLinearMap.comp_apply,independentHistoryLinear_apply]
  simp_rw [vectorCoordinateUpdateLinear_apply]
  rfl

def vectorEuclideanCoordinatesLinear (n k : ℕ) :
    VectorGaussianSpace n k →L[ℝ] VectorGaussianCoordinates n k :=
  ((ContinuousLinearMap.pi fun e : Edge n => EuclideanSpace.proj (.inl (some e))).prod
    (Real.sqrt (1/2 : ℝ) • EuclideanSpace.proj (.inl none))).prod
    (ContinuousLinearMap.pi fun j : Fin (k+2) =>
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.pi fun i : Fin n => EuclideanSpace.proj (.inr (j,i))))

theorem vectorEuclideanCoordinatesLinear_apply (n k : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanCoordinatesLinear n k z=vectorEuclideanCoordinates n k z := by
  rfl

def vectorEuclideanHistoryLinear {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    VectorGaussianSpace n k →L[ℝ] (Fin (k+3) → VectorState n) :=
  (vectorCoordinateHistoryLinear s β t).comp (vectorEuclideanCoordinatesLinear n k)

theorem vectorEuclideanHistoryLinear_apply {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (z : VectorGaussianSpace n k) :
    vectorEuclideanHistoryLinear s β t z=
      vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z) := by
  rw [vectorEuclideanHistoryLinear,ContinuousLinearMap.comp_apply,
    vectorEuclideanCoordinatesLinear_apply,vectorCoordinateHistoryLinear_apply]

def vectorEuclideanStateLinear {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    VectorGaussianSpace n k →L[ℝ] VectorState n :=
  (ContinuousLinearMap.proj (Fin.ofNat (k+3) i)).comp (vectorEuclideanHistoryLinear s β t)

theorem vectorEuclideanStateLinear_apply {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanStateLinear s β t i z=
      vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z) (Fin.ofNat (k+3) i) := by
  rw [vectorEuclideanStateLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,vectorEuclideanHistoryLinear_apply]

end QuantitativePaper
