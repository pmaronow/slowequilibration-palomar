module
public import QuantitativePaper.VectorRecursion

@[expose] public section

/-! All outer disorder integrals in the finite vector interpolation are genuine
integrable Gaussian integrals. Bounds are uniform in the field and recursion depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

private theorem vectorStep_sub_le {n : ℕ} (f g : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (c m R : ℝ)
    (hm : 0 < m) (hfg : ∀ x,f x ≤ g x+R) (x : Field n) :
    vectorColeHopfStep c m f x-vectorColeHopfStep c m g x ≤ R := by
  have hZ : vectorStepPartition c m f x ≤ Real.exp (m*R)*vectorStepPartition c m g x := by
    rw [vectorStepPartition,vectorStepPartition,← integral_const_mul]
    apply integral_mono (integrable_exp_vectorStep f K hf c m x)
      ((integrable_exp_vectorStep g K hg c m x).const_mul _)
    intro z
    calc
      _ ≤ Real.exp (m*(g (fieldShift c x z)+R)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg _) hm.le)
      _ = _ := by rw [mul_add,Real.exp_add];ring
  have hh := Real.log_le_log (vectorStepPartition_pos f K hf c m x) hZ
  rw [Real.log_mul (Real.exp_ne_zero _) (vectorStepPartition_pos g K hg c m x).ne',Real.log_exp] at hh
  unfold vectorColeHopfStep
  rw [ite_eq_right hm.ne',ite_eq_right hm.ne',← sub_div,div_le_iff₀ hm]
  linarith

theorem abs_vectorColeHopfStep_sub_le {n : ℕ} (f g : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (c m R : ℝ)
    (hm : 0 ≤ m) (hfg : ∀ x,|f x-g x| ≤ R) (x : Field n) :
    |vectorColeHopfStep c m f x-vectorColeHopfStep c m g x| ≤ R := by
  by_cases hm0 : m = 0
  · subst m
    simp only [vectorColeHopfStep,ite_true]
    rw [← integral_sub (integrable_vectorStep_input f K hf c x) (integrable_vectorStep_input g K hg c x)]
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := fieldGaussian n) (f := fun z => f (fieldShift c x z)-g (fieldShift c x z))
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hfg (fieldShift c x z))
  · have hp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    rw [abs_le]
    constructor
    · have hh := vectorStep_sub_le g f K hg hf c m R hp (fun y => by
        have hy := (abs_le.mp (hfg y)).1
        linarith) x
      linarith
    · exact vectorStep_sub_le f g K hf hg c m R hp (fun y => by
        have hy := (abs_le.mp (hfg y)).2
        linarith) x

theorem measurable_vectorColeHopfStep_parameter {n : ℕ} {A : Type*} [MeasurableSpace A]
    (f : A → Field n → ℝ) (hf : Measurable (fun p : A × Field n => f p.1 p.2))
    (c m : ℝ) : Measurable (fun p : A × Field n => vectorColeHopfStep c m (f p.1) p.2) := by
  have hshift : Measurable (fun p : (A × Field n) × Field n =>
      (p.1.1,fieldShift c p.1.2 p.2)) := by
    apply Measurable.prodMk
    · fun_prop
    · unfold fieldShift
      fun_prop
  have hF : Measurable (fun p : (A × Field n) × Field n => f p.1.1 (fieldShift c p.1.2 p.2)) := hf.comp hshift
  by_cases hm : m = 0
  · simpa only [vectorColeHopfStep,hm,ite_true] using (hF.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable
  · have he : Measurable (fun p : A × Field n =>
        ∫ z,Real.exp (m*f p.1 (fieldShift c p.2 z)) ∂fieldGaussian n) :=
      ((Real.measurable_exp.comp ((measurable_const (a := m)).mul hF)).stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable
    simpa only [vectorColeHopfStep,ite_eq_right hm,vectorStepPartition,Function.comp_apply] using
      (Real.measurable_log.comp he).div_const m

theorem measurable_vectorRecursion {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    Measurable (fun p : (Couplings n × ℝ) × Field n => vectorRecursion s β t p.1 j p.2) := by
  induction j with
  | zero =>
    unfold vectorRecursion vectorTerminalPotential terminalPotential terminalPartition
      vectorTerminalExponent fieldDot energy Paper.skHamiltonian
    fun_prop
  | succ j ih => exact measurable_vectorColeHopfStep_parameter (fun p x => vectorRecursion s β t p j x) ih _ _

def vectorDisorderEnvelope (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) : ℝ :=
  |β| *Real.sqrt t*(couplingEnvelope n p.1+|p.2|)

theorem vectorRecursion_disorder_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    |vectorRecursion s β t p j x-vectorRecursion s β t (0,0) j x| ≤ vectorDisorderEnvelope n β t p := by
  induction j generalizing x with
  | zero =>
    apply abs_terminalPotential_sub_le
    intro σ
    unfold vectorTerminalExponent vectorDisorderEnvelope
    have hzero : energy n (0 : Couplings n) σ = 0 := by simp [energy,Paper.skHamiltonian]
    rw [hzero]
    simp only [add_zero,add_sub_add_right_eq_sub,mul_zero,sub_zero,abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add (abs_energy_le_envelope n p.1 σ) (le_refl |p.2|))) (by positivity)
  | succ j ih =>
    exact abs_vectorColeHopfStep_sub_le _ _ _ (vectorRecursion_lipschitz s β t p j)
      (vectorRecursion_lipschitz s β t (0,0) j) _ _ _ (s.m_nonneg (Nat.sub_le _ _)) ih x

theorem integrable_exp_vectorDisorderEnvelope (n : ℕ) (β t a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun p => Real.exp (a*vectorDisorderEnvelope n β t p)) (completionLaw n) := by
  have he := (integrable_exp_couplingEnvelope n (a*|β| *Real.sqrt t) (by positivity)).mul_prod
    (FRSB.integrable_exp_mul_abs_gaussian 0 (a*|β| *Real.sqrt t) (1/2) (by positivity))
  change Integrable _ ((couplingLaw n).prod (gaussianReal 0 (1/2)))
  convert he using 1
  ext p
  unfold vectorDisorderEnvelope
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_exp_vectorRecursion {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (j : ℕ) (x : Field n) :
    Integrable (fun p => Real.exp (a*vectorRecursion s β t p j x)) (completionLaw n) := by
  have hmeas : Measurable (fun p : Couplings n × ℝ => vectorRecursion s β t p j x) :=
    (measurable_vectorRecursion s β t j).comp (measurable_id.prodMk measurable_const)
  apply ((integrable_exp_vectorDisorderEnvelope n β t |a| (abs_nonneg _)).const_mul
    (Real.exp (|a| * |vectorRecursion s β t (0,0) j x|))).mono'
    (Real.measurable_exp.comp (measurable_const.mul hmeas)).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  dsimp only [Function.comp_apply,Pi.mul_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hbound := vectorRecursion_disorder_bound s β t p j x
  have habs : |vectorRecursion s β t p j x| ≤
      |vectorRecursion s β t (0,0) j x|+vectorDisorderEnvelope n β t p := by
    have hh := abs_add_le (vectorRecursion s β t (0,0) j x)
      (vectorRecursion s β t p j x-vectorRecursion s β t (0,0) j x)
    rw [add_sub_cancel] at hh
    linarith
  calc
    _ ≤ |a| * |vectorRecursion s β t p j x| := by rw [← abs_mul];exact le_abs_self _
    _ ≤ |a| * (|vectorRecursion s β t (0,0) j x|+vectorDisorderEnvelope n β t p) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = _ := by ring

end QuantitativePaper
