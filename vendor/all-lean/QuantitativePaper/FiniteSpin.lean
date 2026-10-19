module
public import QuantitativePaper.Model
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! Genuine finite spin Gibbs law and its first and second terminal response.
The same finite law supplies the terminal gradient and covariance of the
N-dimensional Parisi recursion. No response identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper

abbrev Field (n : ℕ) := EuclideanSpace ℝ (Fin n)

def fieldDot {n : ℕ} (x : Field n) (σ : Configuration n) : ℝ :=
  ∑ i,x i*Paper.spinSign (σ i)

def terminalPartition {n : ℕ} (E : Configuration n → ℝ) : ℝ := ∑ σ,Real.exp (E σ)
def terminalPotential {n : ℕ} (E : Configuration n → ℝ) : ℝ := Real.log (terminalPartition E)
def terminalWeight {n : ℕ} (E : Configuration n → ℝ) (σ : Configuration n) : ℝ :=
  Real.exp (E σ)/terminalPartition E

def terminalMean {n : ℕ} (E b : Configuration n → ℝ) : ℝ :=
  ∑ σ,terminalWeight E σ*b σ

def terminalCovariance {n : ℕ} (E b d : Configuration n → ℝ) : ℝ :=
  terminalMean E (fun σ => b σ*d σ)-terminalMean E b*terminalMean E d

def terminalTilt {n : ℕ} (E b : Configuration n → ℝ) (y : ℝ) (σ : Configuration n) : ℝ :=
  E σ+y*b σ

def vectorTerminalExponent (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (σ : Configuration n) : ℝ :=
  β*Real.sqrt t*(energy n p.1 σ+p.2)+fieldDot x σ

def vectorTerminalPotential (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) : ℝ :=
  terminalPotential (vectorTerminalExponent n β t p x)

def vectorTerminalMagnetization (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) (x : Field n)
    (i : Fin n) : ℝ := terminalMean (vectorTerminalExponent n β t p x) (fun σ => Paper.spinSign (σ i))

def vectorTerminalCovariance (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  terminalCovariance (vectorTerminalExponent n β t p x)
    (fun σ => Paper.spinSign (σ i)) (fun σ => Paper.spinSign (σ j))

theorem terminalPartition_pos {n : ℕ} (E : Configuration n → ℝ) : 0 < terminalPartition E := by
  unfold terminalPartition
  exact Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty

theorem terminalWeight_pos {n : ℕ} (E : Configuration n → ℝ) (σ : Configuration n) :
    0 < terminalWeight E σ := div_pos (Real.exp_pos _) (terminalPartition_pos E)

theorem terminalWeight_sum {n : ℕ} (E : Configuration n → ℝ) : ∑ σ,terminalWeight E σ = 1 := by
  unfold terminalWeight
  rw [← Finset.sum_div,← terminalPartition,div_self (terminalPartition_pos E).ne']

theorem terminalPMF_sum {n : ℕ} (E : Configuration n → ℝ) :
    ∑ σ,ENNReal.ofReal (terminalWeight E σ) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => (terminalWeight_pos E σ).le),terminalWeight_sum]
  norm_num

def terminalPMF {n : ℕ} (E : Configuration n → ℝ) : PMF (Configuration n) :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (terminalWeight E σ)) (terminalPMF_sum E)
def terminalLaw {n : ℕ} (E : Configuration n → ℝ) : Measure (Configuration n) := (terminalPMF E).toMeasure

instance terminalLaw_probability {n : ℕ} (E : Configuration n → ℝ) : IsProbabilityMeasure (terminalLaw E) :=
  PMF.toMeasure.isProbabilityMeasure _

theorem integral_terminalLaw {n : ℕ} (E b : Configuration n → ℝ) :
    (∫ σ,b σ ∂terminalLaw E) = terminalMean E b := by
  rw [terminalLaw,PMF.integral_eq_sum]
  simp only [terminalPMF,PMF.ofFintype_apply,ENNReal.toReal_ofReal (terminalWeight_pos E _).le,
    smul_eq_mul,terminalMean]

theorem terminalMean_const {n : ℕ} (E : Configuration n → ℝ) (b : ℝ) :
    terminalMean E (fun _ => b) = b := by
  unfold terminalMean
  rw [← Finset.sum_mul,terminalWeight_sum,one_mul]

theorem terminalMean_bound {n : ℕ} (E b : Configuration n → ℝ) (R : ℝ)
    (hb : ∀ σ,|b σ| ≤ R) : |terminalMean E b| ≤ R := by
  unfold terminalMean
  calc
    |∑ σ,terminalWeight E σ*b σ| ≤ ∑ σ,|terminalWeight E σ*b σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ,terminalWeight E σ*R := Finset.sum_le_sum fun σ _ => by
      rw [abs_mul,abs_of_pos (terminalWeight_pos E σ)]
      exact mul_le_mul_of_nonneg_left (hb σ) (terminalWeight_pos E σ).le
    _ = R := by rw [← Finset.sum_mul,terminalWeight_sum,one_mul]

@[simp] theorem terminalTilt_zero {n : ℕ} (E b : Configuration n → ℝ) : terminalTilt E b 0 = E := by
  funext σ
  simp [terminalTilt]

theorem hasDerivAt_terminalPartition_tilt {n : ℕ} (E b : Configuration n → ℝ) (y : ℝ) :
    HasDerivAt (fun r => terminalPartition (terminalTilt E b r))
      (∑ σ,Real.exp (terminalTilt E b y σ)*b σ) y := by
  apply HasDerivAt.fun_sum
  intro σ _
  simpa only [terminalTilt,one_mul,id_eq] using
    (((hasDerivAt_id y).mul_const (b σ)).const_add (E σ)).exp

theorem terminalMean_ratio {n : ℕ} (E b : Configuration n → ℝ) :
    terminalMean E b = (∑ σ,Real.exp (E σ)*b σ)/terminalPartition E := by
  unfold terminalMean terminalWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]

theorem hasDerivAt_terminalPotential_tilt {n : ℕ} (E b : Configuration n → ℝ) (y : ℝ) :
    HasDerivAt (fun r => terminalPotential (terminalTilt E b r))
      (terminalMean (terminalTilt E b y) b) y := by
  rw [terminalMean_ratio]
  exact (hasDerivAt_terminalPartition_tilt E b y).log
    (terminalPartition_pos (terminalTilt E b y)).ne'

private theorem hasDerivAt_terminalWeightedSum_tilt {n : ℕ} (E b d : Configuration n → ℝ) (y : ℝ) :
    HasDerivAt (fun r => ∑ σ,Real.exp (terminalTilt E b r σ)*d σ)
      (∑ σ,Real.exp (terminalTilt E b y σ)*b σ*d σ) y := by
  apply HasDerivAt.fun_sum
  intro σ _
  simpa only [terminalTilt,one_mul,id_eq] using
    ((((hasDerivAt_id y).mul_const (b σ)).const_add (E σ)).exp).mul_const (d σ)

theorem hasDerivAt_terminalMean_tilt {n : ℕ} (E b d : Configuration n → ℝ) (y : ℝ) :
    HasDerivAt (fun r => terminalMean (terminalTilt E b r) d)
      (terminalCovariance (terminalTilt E b y) b d) y := by
  have hh := (hasDerivAt_terminalWeightedSum_tilt E b d y).div
    (hasDerivAt_terminalPartition_tilt E b y) (terminalPartition_pos _).ne'
  have hfun : (fun r => terminalMean (terminalTilt E b r) d) =
      fun r => (∑ σ,Real.exp (terminalTilt E b r σ)*d σ)/terminalPartition (terminalTilt E b r) := by
    funext r
    exact terminalMean_ratio _ _
  rw [hfun]
  have hderiv : terminalCovariance (terminalTilt E b y) b d =
      ((∑ σ,Real.exp (terminalTilt E b y σ)*b σ*d σ)*terminalPartition (terminalTilt E b y)-
      (∑ σ,Real.exp (terminalTilt E b y σ)*d σ)*(∑ σ,Real.exp (terminalTilt E b y σ)*b σ))/
      terminalPartition (terminalTilt E b y)^2 := by
    simp only [terminalCovariance,terminalMean_ratio]
    have hz := (terminalPartition_pos (terminalTilt E b y)).ne'
    have hcross : (∑ σ,Real.exp (terminalTilt E b y σ)*b σ*d σ) =
        ∑ σ,Real.exp (terminalTilt E b y σ)*(b σ*d σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      ring
    rw [hcross]
    field_simp
  rw [hderiv]
  exact hh

@[simp] theorem terminalMean_add {n : ℕ} (E b d : Configuration n → ℝ) :
    terminalMean E (fun σ => b σ+d σ) = terminalMean E b+terminalMean E d := by
  simp only [terminalMean,mul_add,Finset.sum_add_distrib]

@[simp] theorem terminalMean_sub {n : ℕ} (E b d : Configuration n → ℝ) :
    terminalMean E (fun σ => b σ-d σ) = terminalMean E b-terminalMean E d := by
  simp only [terminalMean,mul_sub,Finset.sum_sub_distrib]

@[simp] theorem terminalMean_const_mul {n : ℕ} (E b : Configuration n → ℝ) (r : ℝ) :
    terminalMean E (fun σ => r*b σ) = r*terminalMean E b := by
  simp only [terminalMean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

@[simp] theorem terminalMean_mul_const {n : ℕ} (E b : Configuration n → ℝ) (r : ℝ) :
    terminalMean E (fun σ => b σ*r) = terminalMean E b*r := by
  simp only [terminalMean,Finset.sum_mul,mul_assoc]

@[simp] theorem terminalMean_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (E : Configuration n → ℝ) (b : ι → Configuration n → ℝ) :
    terminalMean E (fun σ => ∑ i,b i σ) = ∑ i,terminalMean E (b i) := by
  unfold terminalMean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem terminalCovariance_centered {n : ℕ} (E b d : Configuration n → ℝ) :
    terminalCovariance E b d = terminalMean E (fun σ =>
      (b σ-terminalMean E b)*(d σ-terminalMean E d)) := by
  have heq : (fun σ => (b σ-terminalMean E b)*(d σ-terminalMean E d)) =
      fun σ => (b σ*d σ-terminalMean E b*d σ)-terminalMean E d*b σ+
        terminalMean E b*terminalMean E d := by
    funext σ
    ring
  rw [heq,terminalMean_add,terminalMean_sub,terminalMean_sub,
    terminalMean_const_mul,terminalMean_const_mul,terminalMean_const]
  unfold terminalCovariance
  ring

theorem terminalCovariance_self_nonneg {n : ℕ} (E b : Configuration n → ℝ) :
    0 ≤ terminalCovariance E b b := by
  rw [terminalCovariance_centered]
  unfold terminalMean
  apply Finset.sum_nonneg
  intro σ _
  have hh := (terminalWeight_pos E σ).le
  exact mul_nonneg hh (mul_self_nonneg _)

theorem terminalCovariance_symm {n : ℕ} (E b d : Configuration n → ℝ) :
    terminalCovariance E b d = terminalCovariance E d b := by
  unfold terminalCovariance
  congr 1
  · congr 1
    funext σ
    ring
  · ring

@[simp] theorem terminalCovariance_sum_left {n : ℕ} {ι : Type*} [Fintype ι]
    (E : Configuration n → ℝ) (b : ι → Configuration n → ℝ) (d : Configuration n → ℝ) :
    terminalCovariance E (fun σ => ∑ i,b i σ) d = ∑ i,terminalCovariance E (b i) d := by
  unfold terminalCovariance
  simp_rw [Finset.sum_mul,terminalMean_sum,Finset.sum_sub_distrib]
  rw [Finset.sum_mul]

@[simp] theorem terminalCovariance_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (E : Configuration n → ℝ) (b : Configuration n → ℝ) (d : ι → Configuration n → ℝ) :
    terminalCovariance E b (fun σ => ∑ i,d i σ) = ∑ i,terminalCovariance E b (d i) := by
  rw [terminalCovariance_symm,terminalCovariance_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact terminalCovariance_symm _ _ _

@[simp] theorem terminalCovariance_const_mul_left {n : ℕ}
    (E b d : Configuration n → ℝ) (r : ℝ) :
    terminalCovariance E (fun σ => r*b σ) d = r*terminalCovariance E b d := by
  have heq : (fun σ => r*b σ*d σ) = fun σ => r*(b σ*d σ) := by
    funext σ
    ring
  unfold terminalCovariance
  rw [heq,terminalMean_const_mul,terminalMean_const_mul]
  ring

@[simp] theorem terminalCovariance_const_mul_right {n : ℕ}
    (E b d : Configuration n → ℝ) (r : ℝ) :
    terminalCovariance E b (fun σ => r*d σ) = r*terminalCovariance E b d := by
  rw [terminalCovariance_symm,terminalCovariance_const_mul_left,terminalCovariance_symm]

theorem vectorTerminalCovariance_quadratic_nonneg (n : ℕ) (β t : ℝ)
    (p : Couplings n × ℝ) (x v : Field n) :
    0 ≤ ∑ i,∑ j,v i*vectorTerminalCovariance n β t p x i j*v j := by
  have hh := terminalCovariance_self_nonneg (vectorTerminalExponent n β t p x) (fieldDot v)
  unfold fieldDot at hh
  simp only [terminalCovariance_sum_left,terminalCovariance_sum_right,
    terminalCovariance_const_mul_left,terminalCovariance_const_mul_right] at hh
  simp_rw [Finset.mul_sum] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold vectorTerminalCovariance
  rw [terminalCovariance_symm]
  ring

theorem vectorTerminalMagnetization_bound (n : ℕ) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (i : Fin n) :
    |vectorTerminalMagnetization n β t p x i| ≤ 1 :=
  terminalMean_bound _ _ 1 (fun σ => by cases σ i <;> norm_num [Paper.spinSign])

theorem fieldDot_basis_line {n : ℕ} (x : Field n) (i : Fin n) (y : ℝ) (σ : Configuration n) :
    fieldDot (x+y • EuclideanSpace.single i 1) σ = fieldDot x σ+y*Paper.spinSign (σ i) := by
  unfold fieldDot
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply]
  simp only [add_mul,Finset.sum_add_distrib]
  congr 1
  simp [mul_ite,ite_mul]

 theorem vectorTerminalExponent_basis_line (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (i : Fin n) (y : ℝ) :
    vectorTerminalExponent n β t p (x+y • EuclideanSpace.single i 1) =
      terminalTilt (vectorTerminalExponent n β t p x) (fun σ => Paper.spinSign (σ i)) y := by
  funext σ
  unfold vectorTerminalExponent terminalTilt
  rw [fieldDot_basis_line]
  ring

theorem hasDerivAt_vectorTerminalPotential_coordinate (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (i : Fin n) :
    HasDerivAt (fun y : ℝ => vectorTerminalPotential n β t p (x+y • EuclideanSpace.single i 1))
      (vectorTerminalMagnetization n β t p x i) 0 := by
  unfold vectorTerminalPotential vectorTerminalMagnetization
  simp_rw [vectorTerminalExponent_basis_line]
  simpa only [terminalTilt_zero] using
    hasDerivAt_terminalPotential_tilt (vectorTerminalExponent n β t p x)
      (fun σ => Paper.spinSign (σ i)) 0

theorem hasDerivAt_vectorTerminalMagnetization_coordinate (n : ℕ) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (i j : Fin n) :
    HasDerivAt (fun y : ℝ => vectorTerminalMagnetization n β t p (x+y • EuclideanSpace.single j 1) i)
      (vectorTerminalCovariance n β t p x i j) 0 := by
  dsimp only [vectorTerminalMagnetization,vectorTerminalCovariance]
  simp_rw [vectorTerminalExponent_basis_line]
  have hh := hasDerivAt_terminalMean_tilt (vectorTerminalExponent n β t p x)
    (fun σ => Paper.spinSign (σ j)) (fun σ => Paper.spinSign (σ i)) 0
  simp only [terminalTilt_zero] at hh
  rw [terminalCovariance_symm] at hh
  exact hh

end QuantitativePaper
