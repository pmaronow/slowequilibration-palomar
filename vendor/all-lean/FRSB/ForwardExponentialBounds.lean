module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Explicit derivative bounds for atom multipliers exp(-delta u).
The recursive constants depend only on the bounds for positive-order
spatial derivatives of u, and retain the essential linear factor delta.
-/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace FRSB

def exponentialDerivativeConstant (K : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K (i + 1) * exponentialDerivativeConstant K (n - i)
termination_by n => n

theorem exponentialDerivativeConstant_nonneg (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) (n : ℕ) :
    0 ≤ exponentialDerivativeConstant K n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [exponentialDerivativeConstant]
    | succ n =>
      rw [exponentialDerivativeConstant]
      exact Finset.sum_nonneg (fun i hi => by
        have hh := ih (n - i) (by omega)
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK _)) hh)

lemma exp_neg_mul_iteratedDeriv_formula (u : ℝ → ℝ) (δ : ℝ)
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => Real.exp (-δ * u y)) x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (-δ * iteratedDeriv (i + 1) u x) * iteratedDeriv (n - i) (fun y => Real.exp (-δ * u y)) x := by
  let f := fun y => Real.exp (-δ * u y)
  let G := fun y => -δ * deriv u y
  have hd : deriv f = G * f := by
    funext y
    have hh := ((hu.differentiable (by simp) y).hasDerivAt).const_mul (-δ) |>.exp
    simpa only [f, G, Pi.mul_apply, mul_comm] using hh.deriv
  have hG : ContDiff ℝ ∞ G :=
    contDiff_const.mul ((contDiff_infty_iff_deriv.mp hu).2)
  have hf : ContDiff ℝ ∞ f := (contDiff_const.mul hu).exp
  rw [iteratedDeriv_succ', hd, iteratedDeriv_mul (hG.of_le (by simp)).contDiffAt (hf.of_le (by simp)).contDiffAt]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [G, f, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']

lemma norm_iteratedDeriv_exp_neg_mul_step (u : ℝ → ℝ) (δ : ℝ)
    (hu : ContDiff ℝ ∞ u) (hδ : 0 ≤ δ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n)
    (hb : ∀ n x, ‖iteratedDeriv (n + 1) u x‖ ≤ K (n + 1))
    (n : ℕ) (x : ℝ)
    (hprevious : ∀ j ≤ n, ‖iteratedDeriv j (fun y => Real.exp (-δ * u y)) x‖ ≤
      exponentialDerivativeConstant K j * Real.exp (-δ * u x)) :
    ‖iteratedDeriv (n + 1) (fun y => Real.exp (-δ * u y)) x‖ ≤
      δ * exponentialDerivativeConstant K (n + 1) * Real.exp (-δ * u x) := by
  rw [exp_neg_mul_iteratedDeriv_formula u δ hu n x]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), ‖(n.choose i : ℝ) * (-δ * iteratedDeriv (i + 1) u x) *
        iteratedDeriv (n - i) (fun y => Real.exp (-δ * u y)) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (δ * K (i + 1)) *
        (exponentialDerivativeConstant K (n - i) * Real.exp (-δ * u x)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_mul, norm_neg, Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hδ]
      have hk := hK (i + 1)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb i x) hδ) (Nat.cast_nonneg _))
        (hprevious (n - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = δ * exponentialDerivativeConstant K (n + 1) * Real.exp (-δ * u x) := by
      rw [exponentialDerivativeConstant]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Every derivative has a relative bound uniform in delta∈[0,1]. -/
theorem norm_iteratedDeriv_exp_neg_mul_le (u : ℝ → ℝ) (δ : ℝ)
    (hu : ContDiff ℝ ∞ u) (hδ : δ ∈ Icc (0 : ℝ) 1)
    (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n)
    (hb : ∀ n x, ‖iteratedDeriv (n + 1) u x‖ ≤ K (n + 1)) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (fun y => Real.exp (-δ * u y)) x‖ ≤
      exponentialDerivativeConstant K j * Real.exp (-δ * u x) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [iteratedDeriv_zero, exponentialDerivativeConstant, Real.norm_of_nonneg (Real.exp_pos _).le]
    | succ n =>
      have hh := norm_iteratedDeriv_exp_neg_mul_step u δ hu hδ.1 K hK hb n x
        (fun j hj => ih j (by omega))
      apply hh.trans
      calc
        _ ≤ 1 * exponentialDerivativeConstant K (n + 1) * Real.exp (-δ * u x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hδ.2 (exponentialDerivativeConstant_nonneg K hK _))
            (Real.exp_pos _).le
        _ = _ := by ring

/-- Positive-order derivatives of an atom multiplier carry a linear delta
factor, independent of the number and positions of other atoms. -/
theorem norm_iteratedDeriv_exp_neg_mul_le_delta (u : ℝ → ℝ) (δ : ℝ)
    (hu : ContDiff ℝ ∞ u) (hδ : δ ∈ Icc (0 : ℝ) 1)
    (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n)
    (hb : ∀ n x, ‖iteratedDeriv (n + 1) u x‖ ≤ K (n + 1)) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv (j + 1) (fun y => Real.exp (-δ * u y)) x‖ ≤
      δ * exponentialDerivativeConstant K (j + 1) * Real.exp (-δ * u x) := by
  exact norm_iteratedDeriv_exp_neg_mul_step u δ hu hδ.1 K hK hb j x
    (fun i _ => norm_iteratedDeriv_exp_neg_mul_le u δ hu hδ K hK hb i x)

end FRSB
