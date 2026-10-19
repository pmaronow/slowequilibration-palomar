module
public import QuantitativePaper.VectorObservableResponse

@[expose] public section

/-! Genuine spatial directional derivatives of the finite vector Parisi
recursion, identified with the constructed terminal-spin responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

theorem fieldDot_add_smul {n : ℕ} (x w : Field n) (y : ℝ) (σ : Configuration n) :
    fieldDot (x+y • w) σ = fieldDot x σ+y*fieldDot w σ := by
  simp only [fieldDot,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

theorem vectorColeHopfStep_translate {n : ℕ} (f : Field n → ℝ) (c m : ℝ)
    (x w : Field n) :
    vectorColeHopfStep c m (fun z => f (z+w)) x = vectorColeHopfStep c m f (x+w) := by
  have he (z : Field n) : fieldShift c x z+w = fieldShift c (x+w) z := by
    unfold fieldShift
    abel
  unfold vectorColeHopfStep vectorStepPartition
  simp_rw [he]

theorem vectorPerturbedRecursion_field_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (w : Field n) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorPerturbedRecursion s β t p (fun σ => fieldDot w σ) j y x =
      vectorRecursion s β t p j (x+y • w) := by
  induction j generalizing x with
  | zero =>
    unfold vectorPerturbedRecursion vectorPerturbedTerminalPotential vectorRecursion vectorTerminalPotential
    congr 1
    funext σ
    unfold terminalTilt vectorTerminalExponent
    rw [fieldDot_add_smul]
    ring
  | succ j ih =>
    simp only [vectorPerturbedRecursion,vectorRecursion]
    have hf : vectorPerturbedRecursion s β t p (fun σ => fieldDot w σ) j y =
        fun z => vectorRecursion s β t p j (z+y • w) := by
      funext z
      exact ih z
    rw [hf,vectorColeHopfStep_translate]

theorem hasDerivAt_vectorRecursion_field_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (w : Field n) (j : ℕ) (y : ℝ) (x : Field n) :
    HasDerivAt (fun r => vectorRecursion s β t p j (x+r • w))
      (vectorObservableResponse s β t p (fun σ => fieldDot w σ) j y x) y := by
  have hb (σ : Configuration n) : |fieldDot w σ| ≤ ((Real.sqrt (n : ℝ)*‖w‖).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact abs_fieldDot w σ
  simpa only [vectorPerturbedRecursion_field_line] using
    hasDerivAt_vectorPerturbedRecursion s β t p (fun σ => fieldDot w σ) _ hb j y x

def vectorMagnetization {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) : Field n :=
  WithLp.toLp 2 (fun i => vectorObservableResponse s β t p (fun σ => Paper.spinSign (σ i)) j 0 x)

theorem vectorMagnetization_component_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    |vectorMagnetization s β t p j x i| ≤ 1 := by
  exact abs_vectorObservableResponse_le s β t p _ 1 (fun σ => by simp) j 0 x

theorem hasDerivAt_vectorRecursion_coordinate {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    HasDerivAt (fun r : ℝ => vectorRecursion s β t p j (x+r • EuclideanSpace.single i 1))
      (vectorMagnetization s β t p j x i) 0 := by
  have he : (fun σ : Configuration n => fieldDot (EuclideanSpace.single i 1) σ) =
      fun σ => Paper.spinSign (σ i) := by
    funext σ
    simp [fieldDot]
  have hh := hasDerivAt_vectorRecursion_field_line s β t p (EuclideanSpace.single i 1) j 0 x
  rw [he] at hh
  exact hh

end QuantitativePaper
