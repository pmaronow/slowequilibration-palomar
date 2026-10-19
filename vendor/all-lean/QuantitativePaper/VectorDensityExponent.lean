module
public import QuantitativePaper.HistoryDensityExponential
public import QuantitativePaper.VectorHistoryProperties

@[expose] public section

/-! The exact Stieltjes-form exponent of the actual vector path density.
The retained-disorder premise of the deterministic path identity is discharged
for every point of the explicit independent Gaussian coordinate construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000

def historyExtended {A : Type*} {N : ℕ} (h : FiniteHistory A N) (i : ℕ) : A :=
  h (Fin.ofNat (N+1) i)

@[simp] theorem historyExtended_fin {A : Type*} {N : ℕ} (h : FiniteHistory A N)
    (i : Fin (N+1)) : historyExtended h i = h i := by
  simp [historyExtended]

def vectorHistoryPotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (h : FiniteHistory (VectorState n) (k+2)) (i : ℕ) : ℝ :=
  vectorRecursion s β t (historyExtended h i).1 (k+2-i) (historyExtended h i).2

theorem historyExtended_left {A : Type*} {N : ℕ} (h : FiniteHistory A N) (i : Fin N) :
    historyExtended h i = h i.castSucc := by
  have he : (i : ℕ) = (i.castSucc : ℕ) := rfl
  rw [he,historyExtended_fin]

theorem historyExtended_right {A : Type*} {N : ℕ} (h : FiniteHistory A N) (i : Fin N) :
    historyExtended h (i+1) = h i.succ := by
  have he : (i : ℕ)+1 = (i.succ : ℕ) := rfl
  rw [he,historyExtended_fin]

theorem vectorProfileWeight_path_eq_exp {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (h : FiniteHistory (VectorState n) (k+2))
    (hp : ∀ i,(h i).1 = (h 0).1) (i : Fin (k+2)) :
    vectorProfileWeight s β t i (h i.castSucc) (h i.succ) =
      ENNReal.ofReal (Real.exp (s.m i*(vectorHistoryPotential s β t h (i+1)-
        vectorHistoryPotential s β t h i))) := by
  rw [vectorProfileWeight_eq_exp s β t i (by omega)]
  unfold vectorHistoryPotential
  rw [historyExtended_left,historyExtended_right]
  have hd : k+2-((i : ℕ)+1)=k+1-i := by omega
  rw [hd,hp i.castSucc,hp i.succ]

theorem vectorProfile_path_density_eq_exp {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (h : FiniteHistory (VectorState n) (k+2))
    (hp : ∀ i,(h i).1 = (h 0).1) :
    finiteHistoryDensity (vectorProfileWeight s β t) (k+2) h =
      ENNReal.ofReal (Real.exp
        (∑ i ∈ Finset.range (k+2),s.m i*(vectorHistoryPotential s β t h (i+1)-
          vectorHistoryPotential s β t h i))) := by
  rw [finiteHistoryDensity_eq_prod]
  simp_rw [vectorProfileWeight_path_eq_exp s β t h hp]
  rw [←ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),←Real.exp_sum]
  congr 2
  exact Fin.sum_univ_eq_sum_range
    (fun i => s.m i*(vectorHistoryPotential s β t h (i+1)-vectorHistoryPotential s β t h i)) _

theorem vectorProfile_path_density_eq_stieltjes {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (h : FiniteHistory (VectorState n) (k+2))
    (hp : ∀ i,(h i).1 = (h 0).1) :
    finiteHistoryDensity (vectorProfileWeight s β t) (k+2) h =
      ENNReal.ofReal (Real.exp (vectorHistoryPotential s β t h (k+2)-
        ∑ i ∈ Finset.range (k+1),(s.m (i+1)-s.m i)*vectorHistoryPotential s β t h (i+1))) := by
  rw [vectorProfile_path_density_eq_exp s β t h hp,weighted_difference_sum s.m _ (k+1)]
  simp only [s.m_top,s.m_zero,one_mul,zero_mul,sub_zero]

theorem vectorHistoryTerminalWeight_eq_exp {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (h : FiniteHistory (VectorState n) (k+2)) (σ : Configuration n) :
    vectorHistoryTerminalWeight s β t h σ = ENNReal.ofReal
      (Real.exp (vectorTerminalExponent n β t (h (Fin.last (k+2))).1
        (h (Fin.last (k+2))).2 σ-vectorHistoryPotential s β t h (k+2))) := by
  unfold vectorHistoryTerminalWeight
  rw [terminalWeight_eq_exp]
  have he : historyExtended h (k+2)=h (Fin.last (k+2)) := by
    simpa only [Fin.val_last] using historyExtended_fin h (Fin.last (k+2))
  simp only [vectorHistoryPotential,he,Nat.sub_self,vectorRecursion,vectorTerminalPotential]

theorem vectorInitialStateWeight_eq_exp {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (h : FiniteHistory (VectorState n) (k+2)) (hzero : (h 0).2=0) :
    vectorInitialStateWeight s β t a (h 0) = ENNReal.ofReal
      (Real.exp (a*vectorHistoryPotential s β t h 0-
        Real.log (vectorOuterPartition (n := n) s β t a))) := by
  have hpot : vectorHistoryPotential s β t h 0 = vectorRecursion s β t (h 0).1 (k+2) 0 := by
    unfold vectorHistoryPotential
    simpa [historyExtended] using
      congrArg (vectorRecursion s β t (h 0).1 (k+2)) hzero
  rw [vectorInitialStateWeight,vectorOuterWeight,Real.exp_sub,
    Real.exp_log (vectorOuterPartition_pos s β t a),hpot]

theorem vectorNormalizedDensity_eq_stieltjes_exp {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (h : FiniteHistory (VectorState n) (k+2)) (σ : Configuration n)
    (hp : ∀ i,(h i).1 = (h 0).1) (hzero : (h 0).2=0) :
    vectorNormalizedDensity s β t a (h,σ) = ENNReal.ofReal
      (Real.exp (vectorTerminalExponent n β t (h (Fin.last (k+2))).1
        (h (Fin.last (k+2))).2 σ-
        (∑ i ∈ Finset.range (k+1),(s.m (i+1)-s.m i)*vectorHistoryPotential s β t h (i+1))+
        a*vectorHistoryPotential s β t h 0-Real.log (vectorOuterPartition (n := n) s β t a))) := by
  rw [vectorNormalizedDensity,vectorFullHistoryDensity,
    vectorInitialStateWeight_eq_exp s β t a h hzero,
    vectorProfile_path_density_eq_stieltjes s β t h hp,vectorHistoryTerminalWeight_eq_exp]
  rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  ring

theorem vectorCoordinateDensity_eq_stieltjes_exp {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (p : VectorGaussianCoordinates n k) (σ : Configuration n) :
    vectorCoordinateDensity s β t a (p,σ) = ENNReal.ofReal
      (Real.exp (vectorTerminalExponent n β t
        (vectorCoordinateHistory s β t p (Fin.last (k+2))).1
        (vectorCoordinateHistory s β t p (Fin.last (k+2))).2 σ-
        (∑ i ∈ Finset.range (k+1),(s.m (i+1)-s.m i)*
          vectorHistoryPotential s β t (vectorCoordinateHistory s β t p) (i+1))+
        a*vectorHistoryPotential s β t (vectorCoordinateHistory s β t p) 0-
        Real.log (vectorOuterPartition (n := n) s β t a))) := by
  exact vectorNormalizedDensity_eq_stieltjes_exp s β t a _ σ
    (fun i => by rw [vectorCoordinateHistory_disorder,vectorCoordinateHistory_initial])
    (by rw [vectorCoordinateHistory_initial])

theorem vectorRecursion_root_eq_of_zero_first_breakpoint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (p : Couplings n × ℝ) (x : Field n) :
    vectorRecursion s β t p (k+2) x=vectorRecursion s β t p (k+1) x := by
  rw [vectorRecursion]
  have h1 : k+2-(k+1)=1 := by omega
  have h0 : k+1-(k+1)=0 := by omega
  rw [h1,h0,hq,s.q_zero]
  simp only [sub_self,mul_zero,vectorColeHopfStep_zero_variance]

theorem vectorCoordinateHistory_one {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hq : s.q 1=0) (p : VectorGaussianCoordinates n k) :
    vectorCoordinateHistory s β t p (1 : Fin (k+3))=(p.1,0) := by
  change vectorCoordinateHistory s β t p (0 : Fin (k+2)).succ=(p.1,0)
  rw [vectorCoordinateHistory_next]
  simp only [Fin.castSucc_zero,Fin.val_zero]
  rw [vectorCoordinateHistory_initial]
  simp [vectorCoordinateUpdate,vectorStateUpdate,fieldShift,hq,s.q_zero]

theorem vectorCoordinateHistoryPotential_root_eq {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (p : VectorGaussianCoordinates n k) :
    vectorHistoryPotential s β t (vectorCoordinateHistory s β t p) 0 =
      vectorHistoryPotential s β t (vectorCoordinateHistory s β t p) 1 := by
  have h0 : historyExtended (vectorCoordinateHistory s β t p) 0=(p.1,0) := by
    simpa [historyExtended] using vectorCoordinateHistory_initial s β t p
  have h1 : historyExtended (vectorCoordinateHistory s β t p) 1=(p.1,0) := by
    have he : (1 : ℕ)=(1 : Fin (k+3)).val := by simp
    rw [he,historyExtended_fin,vectorCoordinateHistory_one s β t hq]
  unfold vectorHistoryPotential
  rw [h0,h1]
  simp only [Nat.sub_zero]
  have hd : k+2-1=k+1 := by omega
  rw [hd]
  exact vectorRecursion_root_eq_of_zero_first_breakpoint s β t hq _ _

theorem vectorCoordinateDensity_eq_floor_exp {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (hq : s.q 1=0) (p : VectorGaussianCoordinates n k) (σ : Configuration n) :
    vectorCoordinateDensity s β t a (p,σ) = ENNReal.ofReal
      (Real.exp (vectorTerminalExponent n β t
        (vectorCoordinateHistory s β t p (Fin.last (k+2))).1
        (vectorCoordinateHistory s β t p (Fin.last (k+2))).2 σ-
        (s.m 1-a)*vectorHistoryPotential s β t (vectorCoordinateHistory s β t p) 1-
        (∑ i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*
          vectorHistoryPotential s β t (vectorCoordinateHistory s β t p) (i+2))-
        Real.log (vectorOuterPartition (n := n) s β t a))) := by
  rw [vectorCoordinateDensity_eq_stieltjes_exp,Finset.sum_range_succ',
    vectorCoordinateHistoryPotential_root_eq s β t hq,s.m_zero]
  simp only [Nat.zero_add,Nat.add_zero,sub_zero]
  congr 2
  ring

theorem vectorFloorCoefficient_nonneg {k : ℕ} (s : RSBScheme k) (a : ℝ)
    (ha : a ≤ s.m 1) : 0 ≤ s.m 1-a := sub_nonneg.mpr ha

theorem vectorStieltjesCoefficient_nonneg {k : ℕ} (s : RSBScheme k)
    {i : ℕ} (hi : i < k) : 0 ≤ s.m (i+2)-s.m (i+1) :=
  sub_nonneg.mpr (s.m_mono (i+1) (by omega))

end QuantitativePaper
