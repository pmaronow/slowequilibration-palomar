module
public import Paper.ParisiFiniteGradientTime
public import Paper.HJBVerification

@[expose] public section

/-! Squared smooth tests for the actual Itô expectation calculation. -/
noncomputable section
open Set MeasureTheory StochasticCalculus Paper
open scoped NNReal ContDiff
namespace FRSB

def itoSquareTest (f : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ := f s x ^ 2

theorem itoSquareTest_timeDerivative (f : ℝ → ℝ → ℝ)
    (ht : ∀ x, Differentiable ℝ (fun s => f s x)) (s x : ℝ) :
    itoTimeDerivative (itoSquareTest f) s x = 2 * f s x * itoTimeDerivative f s x := by
  unfold itoTimeDerivative itoSquareTest
  convert! (((ht x s).hasDerivAt).pow 2).deriv using 1 <;> norm_num

theorem itoSquareTest_spaceDerivative (f : ℝ → ℝ → ℝ)
    (hx : ∀ s, Differentiable ℝ (f s)) (s x : ℝ) :
    itoSpaceDerivative (itoSquareTest f) s x = 2 * f s x * itoSpaceDerivative f s x := by
  unfold itoSpaceDerivative itoSquareTest
  convert! (((hx s x).hasDerivAt).pow 2).deriv using 1 <;> norm_num

theorem itoSquareTest_spaceSecondDerivative (f : ℝ → ℝ → ℝ)
    (hxx : ∀ s, ContDiff ℝ 2 (f s)) (s x : ℝ) :
    itoSpaceSecondDerivative (itoSquareTest f) s x =
      2 * itoSpaceDerivative f s x ^ 2 + 2 * f s x * itoSpaceSecondDerivative f s x := by
  have hdiff : ∀ s, Differentiable ℝ (f s) := fun s => (hxx s).differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv (f s)) := by
    have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) (f s) := by convert! hxx s using 1
    exact (contDiff_succ_iff_deriv.mp h).2.2.differentiable (by norm_num)
  have heq : deriv (itoSquareTest f s) = fun y => 2 * f s y * deriv (f s) y := by
    funext y
    exact itoSquareTest_spaceDerivative f hdiff s y
  unfold itoSpaceSecondDerivative
  rw [heq]
  have h := ((((hdiff s x).hasDerivAt).const_mul 2).mul (hd2 x).hasDerivAt).deriv
  change deriv (fun y => 2 * f s y * deriv (f s) y) x = _ at h
  change deriv (fun y => 2 * f s y * deriv (f s) y) x = _
  rw [h]
  unfold itoSpaceDerivative
  ring

theorem continuous_itoSquareTest (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => itoSquareTest f p.1 p.2) := hf.pow 2

theorem differentiable_itoSquareTest_time (f : ℝ → ℝ → ℝ)
    (ht : ∀ x, Differentiable ℝ (fun s => f s x)) :
    ∀ x, Differentiable ℝ (fun s => itoSquareTest f s x) := fun x => (ht x).pow 2

theorem contDiff_itoSquareTest_spatial (f : ℝ → ℝ → ℝ)
    (hx : ∀ s, ContDiff ℝ 2 (f s)) :
    ∀ s, ContDiff ℝ 2 (itoSquareTest f s) := fun s => (hx s).pow 2

theorem continuous_itoSquareTest_timeDerivative (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (ht : ∀ x, Differentiable ℝ (fun s => f s x))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => itoTimeDerivative (itoSquareTest f) p.1 p.2) := by
  simp_rw [itoSquareTest_timeDerivative f ht]
  exact (hf.const_mul 2).mul hdt

theorem continuous_itoSquareTest_spaceDerivative (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hx : ∀ s, Differentiable ℝ (f s))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (itoSquareTest f) p.1 p.2) := by
  simp_rw [itoSquareTest_spaceDerivative f hx]
  exact (hf.const_mul 2).mul hdx

theorem continuous_itoSquareTest_spaceSecondDerivative (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hx : ∀ s, ContDiff ℝ 2 (f s))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hdxx : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (itoSquareTest f) p.1 p.2) := by
  simp_rw [itoSquareTest_spaceSecondDerivative f hx]
  exact ((hdx.pow 2).const_mul 2).add ((hf.const_mul 2).mul hdxx)

theorem itoSquareTest_generator {Ω : Type*} (X d : ℝ≥0 → Ω → ℝ) (β : ℝ)
    (f : ℝ → ℝ → ℝ) (ht : ∀ x, Differentiable ℝ (fun s => f s x))
    (hx : ∀ s, ContDiff ℝ 2 (f s)) (s : ℝ) (sample : Ω) :
    hjbGenerator X d β (itoSquareTest f) s sample =
      2 * f s (X s.toNNReal sample) * hjbGenerator X d β f s sample +
        β ^ 2 * itoSpaceDerivative f s (X s.toNNReal sample) ^ 2 := by
  unfold hjbGenerator
  rw [itoSquareTest_timeDerivative f ht,
    itoSquareTest_spaceDerivative f (fun s => (hx s).differentiable (by norm_num)),
    itoSquareTest_spaceSecondDerivative f hx]
  ring

theorem norm_itoSquareTest_spaceDerivative_le (f : ℝ → ℝ → ℝ)
    (hx : ∀ s, Differentiable ℝ (f s)) {R K : ℝ}
    (hf : ∀ s x, ‖f s x‖ ≤ R) (hdx : ∀ s x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (s x : ℝ) : ‖itoSpaceDerivative (itoSquareTest f) s x‖ ≤ 2 * R * K := by
  rw [itoSquareTest_spaceDerivative f hx, norm_mul, norm_mul,
    show ‖(2 : ℝ)‖ = 2 by norm_num]
  have hR : 0 ≤ R := (norm_nonneg _).trans (hf s x)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hf s x) (by norm_num)) (hdx s x)
    (norm_nonneg _) (by positivity)

end FRSB
