module
public import QuantitativePaper.VectorHessianComparison
public import QuantitativePaper.VectorGradient
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Actual joint convexity of the finite vector Parisi potential in disorder
and field. Every line derivative is the constructed spin response, whose
second derivative is nonnegative by the proved covariance comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

abbrev VectorParameter (n : ℕ) := (Couplings n × ℝ) × Field n

theorem energy_add_smul (n : ℕ) (g w : Couplings n) (y : ℝ)
    (σ : Configuration n) : energy n (g+y • w) σ = energy n g σ+y*energy n w σ := by
  unfold energy Paper.skHamiltonian
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,
    mul_assoc,zero_mul,add_zero]
  have he : (∑ e : Edge n,y*(w e*(Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)))) =
      y*∑ e : Edge n,w e*(Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)) := by
    rw [Finset.mul_sum]
  rw [he]
  ring

theorem vectorTerminalExponent_joint_line {n : ℕ} (β t : ℝ) (p w : Couplings n × ℝ)
    (x v : Field n) (y : ℝ) (σ : Configuration n) :
    vectorTerminalExponent n β t (p+y • w) (x+y • v) σ =
      vectorTerminalExponent n β t p x σ+y*vectorTerminalExponent n β t w v σ := by
  unfold vectorTerminalExponent
  change β*Real.sqrt t*(energy n (p.1+y • w.1) σ+(p.2+y*w.2))+fieldDot (x+y • v) σ = _
  rw [energy_add_smul,fieldDot_add_smul]
  ring

theorem vectorPerturbedRecursion_joint_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p w : Couplings n × ℝ) (x v : Field n) (j : ℕ) (y : ℝ) :
    vectorPerturbedRecursion s β t p (vectorTerminalExponent n β t w v) j y x =
      vectorRecursion s β t (p+y • w) j (x+y • v) := by
  induction j generalizing x with
  | zero =>
    unfold vectorPerturbedRecursion vectorPerturbedTerminalPotential vectorRecursion vectorTerminalPotential
    congr 1
    funext σ
    exact (vectorTerminalExponent_joint_line β t p w x v y σ).symm
  | succ j ih =>
    simp only [vectorPerturbedRecursion,vectorRecursion]
    have he : vectorPerturbedRecursion s β t p (vectorTerminalExponent n β t w v) j y =
        fun z => vectorRecursion s β t (p+y • w) j (z+y • v) := by
      funext z
      exact ih z
    rw [he,vectorColeHopfStep_translate]

def jointDirectionBound {n : ℕ} (β t : ℝ) (w : VectorParameter n) : ℝ≥0 :=
  (∑ σ : Configuration n,|vectorTerminalExponent n β t w.1 w.2 σ|).toNNReal

theorem vectorTerminalExponent_le_jointDirectionBound {n : ℕ} (β t : ℝ)
    (w : VectorParameter n) (σ : Configuration n) :
    |vectorTerminalExponent n β t w.1 w.2 σ| ≤ jointDirectionBound β t w := by
  unfold jointDirectionBound
  rw [Real.coe_toNNReal _ (by positivity)]
  exact Finset.single_le_sum (f := fun σ => |vectorTerminalExponent n β t w.1 w.2 σ|)
    (fun σ _ => abs_nonneg _) (Finset.mem_univ σ)

theorem hasDerivAt_vectorRecursion_joint_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p w : VectorParameter n) (j : ℕ) (y : ℝ) :
    HasDerivAt (fun r => vectorRecursion s β t (p.1+r • w.1) j (p.2+r • w.2))
      (vectorObservableResponse s β t p.1 (vectorTerminalExponent n β t w.1 w.2) j y p.2) y := by
  simpa only [vectorPerturbedRecursion_joint_line] using
    hasDerivAt_vectorPerturbedRecursion s β t p.1 (vectorTerminalExponent n β t w.1 w.2)
      (jointDirectionBound β t w) (vectorTerminalExponent_le_jointDirectionBound β t w) j y p.2

theorem convexOn_vectorRecursion_joint_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p w : VectorParameter n) (j : ℕ) :
    ConvexOn ℝ univ (fun r : ℝ => vectorRecursion s β t (p.1+r • w.1) j (p.2+r • w.2)) := by
  let f := fun r : ℝ => vectorRecursion s β t (p.1+r • w.1) j (p.2+r • w.2)
  let b := vectorTerminalExponent n β t w.1 w.2
  let V := fun y => vectorObservableResponse s β t p.1 b j y p.2
  let H := fun y => vectorObservableSecondResponse s β t p.1 b j y p.2
  have hd (y : ℝ) : HasDerivAt f (V y) y := hasDerivAt_vectorRecursion_joint_line s β t p w j y
  have hv (y : ℝ) : HasDerivAt V (H y) y := hasDerivAt_vectorObservableResponse s β t p.1 b
    (jointDirectionBound β t w) (vectorTerminalExponent_le_jointDirectionBound β t w) j y p.2
  have hderiv : deriv f = V := funext (fun y => (hd y).deriv)
  have hn (y : ℝ) : 0 ≤ H y := by
    have hC := vectorObservableCovariance_nonneg s β t p.1 b (jointDirectionBound β t w)
      (vectorTerminalExponent_le_jointDirectionBound β t w) j y p.2
    have hHC := (vectorObservableSecondResponse_covariance_bounds s β t p.1 b
      (jointDirectionBound β t w) (vectorTerminalExponent_le_jointDirectionBound β t w) j y p.2).1
    exact (mul_nonneg (observableDepthMass_nonneg s j) hC).trans hHC
  apply convexOn_univ_of_deriv2_nonneg (fun y => (hd y).differentiableAt)
  · rw [hderiv]
    exact fun y => (hv y).differentiableAt
  · intro y
    change 0 ≤ deriv (deriv f) y
    rw [hderiv,(hv y).deriv]
    exact hn y

theorem convexOn_vectorRecursion_joint {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    ConvexOn ℝ univ (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) := by
  refine ⟨convex_univ,?_⟩
  intro p hp z hz a b ha hb hab
  have hc := convexOn_vectorRecursion_joint_line s β t p (z-p) j
  have hh := hc.2 (mem_univ 0) (mem_univ 1) ha hb hab
  have he : p+b • (z-p) = a • p+b • z := by
    calc
      p+b • (z-p) = (1-b) • p+b • z := by module
      _ = a • p+b • z := by congr 2;linarith
  have hp' : p.1+b • (z.1-p.1) = (a • p+b • z).1 := congrArg Prod.fst he
  have hx' : p.2+b • (z.2-p.2) = (a • p+b • z).2 := congrArg Prod.snd he
  simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,one_smul,
    add_zero,add_sub_cancel,Prod.fst_sub,Prod.snd_sub,hp',hx'] using hh

end QuantitativePaper
