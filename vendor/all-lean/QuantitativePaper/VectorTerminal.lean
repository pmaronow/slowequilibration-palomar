module
public import QuantitativePaper.FiniteSpin
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

/-! Sharp field Lipschitz bounds and genuine Gaussian integrability of the
finite N-vector terminal potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace NNReal
namespace QuantitativePaper

abbrev fieldGaussian (n : ℕ) : Measure (Field n) :=
  SYK.standardGaussianMeasureOnEuclidean (Fin n)

def spinVector {n : ℕ} (σ : Configuration n) : Field n :=
  WithLp.toLp 2 (fun i => Paper.spinSign (σ i))

theorem norm_spinVector {n : ℕ} (σ : Configuration n) :
    ‖spinVector σ‖ = Real.sqrt (n : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [spinVector]

theorem fieldDot_eq_inner {n : ℕ} (x : Field n) (σ : Configuration n) :
    fieldDot x σ = inner ℝ x (spinVector σ) := by
  simp [fieldDot,spinVector,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem abs_fieldDot {n : ℕ} (x : Field n) (σ : Configuration n) :
    |fieldDot x σ| ≤ Real.sqrt (n : ℝ)*‖x‖ := by
  rw [fieldDot_eq_inner]
  exact (abs_real_inner_le_norm _ _).trans_eq (by rw [norm_spinVector,mul_comm])

theorem fieldDot_sub {n : ℕ} (x y : Field n) (σ : Configuration n) :
    fieldDot x σ-fieldDot y σ = fieldDot (x-y) σ := by
  simp only [fieldDot,PiLp.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem terminalPotential_le_of_pointwise_add {n : ℕ} (E F : Configuration n → ℝ) (R : ℝ)
    (hEF : ∀ σ,E σ ≤ F σ+R) : terminalPotential E ≤ terminalPotential F+R := by
  have hsum : terminalPartition E ≤ Real.exp R*terminalPartition F := by
    unfold terminalPartition
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    calc
      _ ≤ Real.exp (F σ+R) := Real.exp_le_exp.mpr (hEF σ)
      _ = _ := by rw [Real.exp_add];ring
  have hh := Real.log_le_log (terminalPartition_pos E) hsum
  rw [Real.log_mul (Real.exp_ne_zero _) (terminalPartition_pos F).ne',Real.log_exp] at hh
  unfold terminalPotential
  linarith

theorem abs_terminalPotential_sub_le {n : ℕ} (E F : Configuration n → ℝ) (R : ℝ)
    (hEF : ∀ σ,|E σ-F σ| ≤ R) : |terminalPotential E-terminalPotential F| ≤ R := by
  rw [abs_le]
  constructor
  · have hh := terminalPotential_le_of_pointwise_add F E R (fun σ => by
      have hs := (abs_le.mp (hEF σ)).1
      linarith)
    linarith
  · have hh := terminalPotential_le_of_pointwise_add E F R (fun σ => by
      have hs := (abs_le.mp (hEF σ)).2
      linarith)
    linarith

theorem vectorTerminalPotential_lipschitz (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorTerminalPotential n β t p) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  apply abs_terminalPotential_sub_le
  intro σ
  unfold vectorTerminalExponent
  rw [add_sub_add_left_eq_sub,fieldDot_sub]
  exact abs_fieldDot _ _

theorem integrable_exp_vectorTerminalPotential (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) (a : ℝ) :
    Integrable (fun x => Real.exp (a*vectorTerminalPotential n β t p x)) (fieldGaussian n) := by
  apply SYK.integrable_exp_smul_lipschitz _ (Real.sqrt (n : ℝ)+1) (by positivity) _ a
  exact (vectorTerminalPotential_lipschitz n β t p).weaken (by
    apply Real.toNNReal_le_toNNReal
    linarith)

theorem integrable_vectorTerminalPotential (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) :
    Integrable (vectorTerminalPotential n β t p) (fieldGaussian n) := by
  apply (integrable_norm_iff (vectorTerminalPotential_lipschitz n β t p).continuous.aestronglyMeasurable).mp
  simpa only [pow_one,Real.norm_eq_abs] using
    integrable_pow_abs_of_integrable_exp_mul one_ne_zero
      (integrable_exp_vectorTerminalPotential n β t p 1)
      (integrable_exp_vectorTerminalPotential n β t p (-1)) 1

end QuantitativePaper
