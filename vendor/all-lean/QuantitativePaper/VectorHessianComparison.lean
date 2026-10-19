module
public import QuantitativePaper.VectorConditionalMean

@[expose] public section

/-! Genuine finite-vector second variation/covariance comparison. The actual
second derivatives obey a C ≤ H ≤ C, with a the mass of the current cell. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

def observableDepthMass {k : ℕ} (s : RSBScheme k) (j : ℕ) : ℝ :=
  if j = 0 then 1 else s.m (k+2-j)

@[simp] theorem observableDepthMass_succ {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    observableDepthMass s (j+1) = s.m (k+1-j) := by
  simp only [observableDepthMass,Nat.add_one_ne_zero,ite_false]
  congr 1
  omega

theorem observableDepthMass_nonneg {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    0 ≤ observableDepthMass s j := by
  cases j with
  | zero => simp [observableDepthMass]
  | succ j => rw [observableDepthMass_succ];exact s.m_nonneg (Nat.sub_le _ _)

theorem observableDepthMass_le_one {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    observableDepthMass s j ≤ 1 := by
  cases j with
  | zero => simp [observableDepthMass]
  | succ j => rw [observableDepthMass_succ];exact s.m_le_one (Nat.sub_le _ _)

theorem observableDepthMass_step_le {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    s.m (k+1-j) ≤ observableDepthMass s j := by
  cases j with
  | zero => simp [observableDepthMass,s.m_top]
  | succ j =>
    rw [observableDepthMass_succ]
    exact s.m_mono' (k+1-j) (Nat.sub_le _ _) (k+1-(j+1)) (by omega)

private theorem expectation_covariance_step {n : ℕ} (f v H C : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (hH : Measurable H) (hC : Measurable C)
    (R S T : ℝ) (hvB : ∀ z,|v z| ≤ R) (hHB : ∀ z,|H z| ≤ S) (hCB : ∀ z,|C z| ≤ T)
    (a m : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hma : m ≤ a)
    (hCn : ∀ z,0 ≤ C z) (hHC : ∀ z,a*C z ≤ H z ∧ H z ≤ C z)
    (c : ℝ) (x : Field n) :
    let E := fun w => vectorStepResponse c m f w x
    let V := E (fun z => v z^2)-(E v)^2
    m*(E C+V) ≤ E H+m*V ∧ E H+m*V ≤ E C+V := by
  dsimp only
  have hleft := vectorStepResponse_mono f (fun z => m*C z) H K hf
    (measurable_const.mul hC) hH (|m| * T) S
    (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hCB z) (abs_nonneg m)) hHB
    (fun z => (mul_le_mul_of_nonneg_right hma (hCn z)).trans (hHC z).1) c m x
  rw [vectorStepResponse_mul_const] at hleft
  have hright := vectorStepResponse_mono f H C K hf hH hC S T hHB hCB (fun z => (hHC z).2) c m x
  have hvar := vectorStepResponse_variance_nonneg f v K hf hv R hvB c m x
  have hmul := mul_le_mul_of_nonneg_right hm1 hvar
  constructor <;> nlinarith

theorem vectorObservableSecondResponse_covariance_bounds {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    observableDepthMass s j*vectorObservableCovariance s β t p b j y x ≤
      vectorObservableSecondResponse s β t p b j y x ∧
    vectorObservableSecondResponse s β t p b j y x ≤ vectorObservableCovariance s β t p b j y x := by
  have hb2 : ∀ σ,|b σ^2| ≤ (R : ℝ)^2 := by
    intro σ
    rw [abs_sq]
    have hh := mul_self_le_mul_self (abs_nonneg _) (hb σ)
    simpa [←pow_two] using hh
  induction j generalizing x with
  | zero =>
    have he : vectorObservableSecondResponse s β t p b 0 y x = vectorObservableCovariance s β t p b 0 y x := by
      simp only [vectorObservableSecondResponse,vectorObservableCovariance,vectorConditionalMean,
        vectorObservableResponse,vectorTerminalObservable,terminalCovariance,pow_two]
    rw [he]
    simp [observableDepthMass]
  | succ j ih =>
    let f := vectorPerturbedRecursion s β t p b j y
    let v := vectorObservableResponse s β t p b j y
    let w := vectorConditionalMean s β t p b (fun σ => b σ^2) j y
    let H := vectorObservableSecondResponse s β t p b j y
    let C := vectorObservableCovariance s β t p b j y
    let c := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let m := s.m (k+1-j)
    have hf := vectorPerturbedRecursion_lipschitz s β t p b j y
    have hv : Measurable v := (measurable_vectorObservableResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hw : Measurable w := (measurable_vectorConditionalMean s β t p b _ j).comp
      (measurable_const.prodMk measurable_id)
    have hH : Measurable H := (measurable_vectorObservableSecondResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hC : Measurable C := (measurable_vectorObservableCovariance s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hvB : ∀ z,|v z| ≤ R := fun z => abs_vectorObservableResponse_le s β t p b R hb j y z
    have hv2B : ∀ z,|v z^2| ≤ (R : ℝ)^2 := by
      intro z
      rw [abs_sq]
      have hh := mul_self_le_mul_self (abs_nonneg _) (hvB z)
      simpa [←pow_two] using hh
    have hwB : ∀ z,|w z| ≤ (R : ℝ)^2 := fun z => abs_vectorConditionalMean_le s β t p b _ _ hb2 j y z
    have hHB : ∀ z,|H z| ≤ observableSecondBound R j := fun z => abs_vectorObservableSecondResponse_le s β t p b R hb j y z
    have hCB : ∀ z,|C z| ≤ (R : ℝ)^2 := fun z => abs_vectorObservableCovariance_le s β t p b R hb j y z
    have hCn : ∀ z,0 ≤ C z := fun z => vectorObservableCovariance_nonneg s β t p b R hb j y z
    have hmean : vectorStepResponse c m f C x = vectorStepResponse c m f w x-
        vectorStepResponse c m f (fun z => v z^2) x :=
      vectorStepResponse_sub f w (fun z => v z^2) _ hf hw (hv.pow_const 2) _ _ hwB hv2B c m x
    have hstep := expectation_covariance_step f v H C _ hf hv hH hC R (observableSecondBound R j)
      ((R : ℝ)^2) hvB hHB hCB (observableDepthMass s j) m (s.m_nonneg (Nat.sub_le _ _))
      (s.m_le_one (Nat.sub_le _ _)) (observableDepthMass_step_le s j) hCn ih c x
    dsimp only at hstep
    rw [hmean] at hstep
    rw [observableDepthMass_succ]
    change m*(vectorStepResponse c m f w x-(vectorStepResponse c m f v x)^2) ≤
        vectorStepSecondResponse c m f v H x ∧
      vectorStepSecondResponse c m f v H x ≤ vectorStepResponse c m f w x-(vectorStepResponse c m f v x)^2
    unfold vectorStepSecondResponse
    constructor <;> nlinarith [hstep.1,hstep.2]

end QuantitativePaper
