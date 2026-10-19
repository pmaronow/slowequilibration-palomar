module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

/-!
# Homogeneous Volterra row uniqueness

This proves uniqueness from the differential equation itself using the
nonnegative energy `f(t)^2 + ∫ f(u)^2`. It does not presume a zero solution.
Only the kernel's interval integrability and its finite-horizon bound are
required; the kernel need not have a derivative.
-/

noncomputable section
open Set MeasureTheory

namespace SphericalAging.VolterraUniqueness

theorem two_mul_kernel_le (a b k S : ℝ) (hk : |k| ≤ S) :
    2 * a * k * b ≤ S * (a ^ 2 + b ^ 2) := by
  by_cases hk0 : 0 ≤ k
  · calc
      2 * a * k * b = k * (2 * a * b) := by ring
      _ ≤ k * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (a - b)]) hk0
      _ ≤ S * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_right ((le_abs_self k).trans hk)
          (add_nonneg (sq_nonneg a) (sq_nonneg b))
  · have hkneg : 0 ≤ -k := by linarith
    calc
      2 * a * k * b = (-k) * (-2 * a * b) := by ring
      _ ≤ (-k) * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (a + b)]) hkneg
      _ ≤ S * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_right ((neg_le_abs k).trans hk)
          (add_nonneg (sq_nonneg a) (sq_nonneg b))

/-- A continuous row satisfying a homogeneous Volterra differential equation
with zero initial value is zero on every bounded causal interval.

Global continuity is convenient for primitive calculus. Applications may
extend a row continuously outside the interval; no equation is required
outside `[a,T)`. -/
theorem homogeneous_row_eq_zero
    (f f' ell : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (a T L S : ℝ)
    (haT : a ≤ T) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hf : Continuous f) (ha : f a = 0)
    (hderiv : ∀ t ∈ Ico a T, HasDerivWithinAt f (f' t) (Ici t) t)
    (heq : ∀ t ∈ Ico a T,
      f' t = -ell t * f t + ∫ u in a..t, K t u * f u)
    (hell : ∀ t ∈ Ico a T, |ell t| ≤ L)
    (hKint : ∀ t ∈ Ico a T,
      IntervalIntegrable (fun u => K t u * f u) volume a t)
    (hK : ∀ t ∈ Ico a T, ∀ u ∈ Icc a t, |K t u| ≤ S) :
    ∀ t ∈ Icc a T, f t = 0 := by
  let F : ℝ → ℝ := fun t => ∫ u in a..t, f u ^ 2
  let E : ℝ → ℝ := fun t => f t ^ 2 + F t
  let A : ℝ := 2 * L + S * (T - a) + 1
  let B : ℝ := A + S
  have hsq : Continuous (fun t => f t ^ 2) := hf.pow 2
  have hFderiv (t : ℝ) : HasDerivAt F (f t ^ 2) t :=
    intervalIntegral.integral_hasDerivAt_right (hsq.intervalIntegrable a t)
      hsq.aestronglyMeasurable.stronglyMeasurableAtFilter hsq.continuousAt
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hFderiv t).continuousAt)
  have hEcont : Continuous E := hsq.add hFcont
  have hFnonneg (t : ℝ) (ht : a ≤ t) : 0 ≤ F t :=
    intervalIntegral.integral_nonneg ht (fun _ _ => sq_nonneg _)
  have hEnonneg (t : ℝ) (ht : a ≤ t) : 0 ≤ E t :=
    add_nonneg (sq_nonneg _) (hFnonneg t ht)
  have hEderiv (t : ℝ) (ht : t ∈ Ico a T) :
      HasDerivWithinAt E (2 * f t * f' t + f t ^ 2) (Ici t) t := by
    convert! ((hderiv t ht).pow 2).add (hFderiv t).hasDerivWithinAt using 1
    norm_num
  have hEbound (t : ℝ) (ht : t ∈ Ico a T) :
      2 * f t * f' t + f t ^ 2 ≤ B * E t := by
    have hmemory : 2 * f t * (∫ u in a..t, K t u * f u) ≤
        S * ((t - a) * f t ^ 2 + F t) := by
      have hright : IntervalIntegrable (fun u => S * (f t ^ 2 + f u ^ 2)) volume a t :=
        ((continuous_const.add hsq).const_mul S).intervalIntegrable a t
      have hi := intervalIntegral.integral_mono_on ht.1
        ((hKint t ht).const_mul (2 * f t)) hright
        (fun u hu => by
          simpa only [mul_assoc] using
            two_mul_kernel_le (f t) (f u) (K t u) S (hK t ht u hu))
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const (hsq.intervalIntegrable a t),
        intervalIntegral.integral_const] at hi
      simpa only [smul_eq_mul] using hi
    have hellbound : -2 * ell t * f t ^ 2 ≤ 2 * L * f t ^ 2 := by
      have h := mul_le_mul_of_nonneg_right ((neg_le_abs (ell t)).trans (hell t ht))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (f t)))
      nlinarith only [h]
    have htime : S * (t - a) * f t ^ 2 ≤ S * (T - a) * f t ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) hS) (sq_nonneg _)
    have hfirst : 2 * f t * f' t + f t ^ 2 ≤ A * f t ^ 2 + S * F t := by
      rw [heq t ht]
      dsimp [A]
      nlinarith only [hmemory, hellbound, htime]
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hAB : A ≤ B := by dsimp [B]; linarith
    have hSB : S ≤ B := by dsimp [B]; linarith
    calc
      2 * f t * f' t + f t ^ 2 ≤ A * f t ^ 2 + S * F t := hfirst
      _ ≤ B * f t ^ 2 + B * F t := add_le_add
        (mul_le_mul_of_nonneg_right hAB (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hSB (hFnonneg t ht.1))
      _ = B * E t := by dsimp [E]; ring
  have hEzero : E a = 0 := by simp [E, F, ha]
  have hbound := le_gronwallBound_of_liminf_deriv_right_le (δ := 0) (K := B) (ε := 0)
    hEcont.continuousOn
    (fun t ht r hr => (hEderiv t ht).liminf_right_slope_le hr)
    (show E a ≤ 0 by simp [hEzero]) (fun t ht => by simpa using hEbound t ht)
  intro t ht
  have hEt : E t ≤ 0 := by simpa only [gronwallBound_ε0_δ0] using hbound t ht
  have hft : f t ^ 2 ≤ 0 := by
    have hFn := hFnonneg t ht.1
    dsimp [E] at hEt
    linarith
  nlinarith [sq_nonneg (f t)]

/-- The finite-horizon version only assumes continuity on the actual row.
Clamping supplies the harmless global extension needed for primitive calculus.
The equation and derivative assumptions remain on the causal interval. -/
theorem homogeneous_row_eq_zero_on
    (f f' ell : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (a T L S : ℝ)
    (haT : a ≤ T) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hf : ContinuousOn f (Icc a T)) (ha : f a = 0)
    (hderiv : ∀ t ∈ Ico a T, HasDerivWithinAt f (f' t) (Ici t) t)
    (heq : ∀ t ∈ Ico a T,
      f' t = -ell t * f t + ∫ u in a..t, K t u * f u)
    (hell : ∀ t ∈ Ico a T, |ell t| ≤ L)
    (hKint : ∀ t ∈ Ico a T,
      IntervalIntegrable (fun u => K t u * f u) volume a t)
    (hK : ∀ t ∈ Ico a T, ∀ u ∈ Icc a t, |K t u| ≤ S) :
    ∀ t ∈ Icc a T, f t = 0 := by
  let clamp : ℝ → ℝ := fun t => max a (min T t)
  let g : ℝ → ℝ := fun t => f (clamp t)
  have hclamp : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hmem (t : ℝ) : clamp t ∈ Icc a T :=
    ⟨le_max_left _ _, max_le haT (min_le_left _ _)⟩
  have hgcont : Continuous g := hf.comp_continuous hclamp hmem
  have hg (t : ℝ) (ht : t ∈ Icc a T) : g t = f t := by
    dsimp [g, clamp]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hgderiv (t : ℝ) (ht : t ∈ Ico a T) :
      HasDerivWithinAt g (f' t) (Ici t) t := by
    apply (hderiv t ht).congr_of_eventuallyEq _ (hg t ⟨ht.1, ht.2.le⟩)
    filter_upwards [(eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hut htu
    exact hg u ⟨ht.1.trans htu, hut.le⟩
  have hgK (t : ℝ) (ht : t ∈ Ico a T) :
      Set.EqOn (fun u => K t u * g u) (fun u => K t u * f u) (uIcc a t) := by
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only
    rw [hg u ⟨hu.1, hu.2.trans ht.2.le⟩]
  have hgint (t : ℝ) (ht : t ∈ Ico a T) :
      IntervalIntegrable (fun u => K t u * g u) volume a t := by
    apply (hKint t ht).congr_uIoo
    intro u hu
    exact (hgK t ht (uIoo_subset_uIcc_self hu)).symm
  have hgeq (t : ℝ) (ht : t ∈ Ico a T) :
      f' t = -ell t * g t + ∫ u in a..t, K t u * g u := by
    rw [hg t ⟨ht.1, ht.2.le⟩, intervalIntegral.integral_congr (hgK t ht)]
    exact heq t ht
  have hga : g a = 0 := (hg a ⟨le_refl a, haT⟩).trans ha
  have hzero := homogeneous_row_eq_zero g f' ell K a T L S haT hL hS
    hgcont hga hgderiv hgeq hell hgint hK
  intro t ht
  simpa only [hg t ht] using hzero t ht

end SphericalAging.VolterraUniqueness
