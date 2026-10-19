module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedScheme
public import Targets.Section4InsertedScheme

@[expose] public section

/-! Covariance-independent RSB correction algebra.

These finite sums are valid for any scalar θ with θ(0)=0. Insertion and
merging genuinely preserve the corresponding actual correction. Algebraic
arguments are adapted from the Apache 2.0 `SecondInterpolationAlgebra` and
`RSBSchemeMassReduction` sources without their quadratic specialization.
-/
noncomputable section
open Real
open SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

def schemeCorrection (θ : ℝ → ℝ) {k : ℕ} (s : RSBScheme k) : ℝ :=
  (1 / 2) * ∑ p ∈ Finset.range (k + 2), s.m p * (θ (s.q (p + 1)) - θ (s.q p))

theorem schemeCorrection_telescope (θ : ℝ → ℝ) (hθ : θ 0 = 0)
    {k : ℕ} (s : RSBScheme k) :
    schemeCorrection θ s = (1 / 2) * (θ 1 -
      ∑ p ∈ Finset.range (k + 1), (s.m (p + 1) - s.m p) * θ (s.q (p + 1))) := by
  have H := Finset.sum_range_by_parts s.m
    (fun p => θ (s.q (p + 1)) - θ (s.q p)) (k + 2)
  simp_rw [Finset.sum_range_sub (fun p => θ (s.q p))] at H
  simp only [s.q_zero, hθ, sub_zero, show k + 2 - 1 = k + 1 by omega, s.m_top,
    s.q_top, smul_eq_mul, one_mul] at H
  exact congrArg (fun z : ℝ => (1 / 2) * z) H

@[simp] theorem AdmissibleEvenMixture.correction_zero (ξ : AdmissibleEvenMixture) :
    ξ.correction 0 = 0 := by simp [AdmissibleEvenMixture.correction, ξ.value_zero]

theorem mixedSchemeCorrection_eq_schemeCorrection (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) :
    mixedSchemeCorrection ξ s = schemeCorrection ξ.correction s := by
  rw [schemeCorrection_telescope ξ.correction ξ.correction_zero,
    mixedSchemeCorrection, mixedScheme_correction_mass_sum,
    Fin.sum_univ_eq_sum_range (fun i => (s.m (i + 1) - s.m i) * ξ.correction (s.q (i + 1)))]

/-- Splitting one interval changes the correction by its genuine θ increment. -/
theorem schemeCorrection_insertLevel (θ : ℝ → ℝ) {k : ℕ} (s : RSBScheme k)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    schemeCorrection θ (s.insertLevel r hr0 hr m u hm hu) =
      schemeCorrection θ s + (m - s.m (r - 1)) / 2 * (θ (s.q r) - θ u) := by
  let f := fun p => section4Mass s r m p *
    (θ (section5Rho s r u (p + 1)) - θ (section5Rho s r u p))
  let g := fun p => s.m p * (θ (s.q (p + 1)) - θ (s.q p))
  let δ := (m - s.m (r - 1)) * (θ (s.q r) - θ u)
  have hbefore (p : ℕ) (hp : p + 1 < r) : f p = g p := by
    simp only [f, g, section4Mass, section5Rho, ite_eq_left (by omega : p < r), ite_eq_left hp]
  have hsplit : f (r - 1) = s.m (r - 1) * (θ u - θ (s.q (r - 1))) := by
    have hi : r - 1 + 1 = r := by omega
    simp only [f, section4Mass, section5Rho, hi, ite_eq_left (by omega : r - 1 < r),
      lt_self_iff_false, ite_false, ite_true]
  have hnew : f r = m * (θ (s.q r) - θ u) := by
    simp [f, section4Mass, section5Rho, show ¬r + 1 < r by omega]
  have hafter (p : ℕ) (hp : r < p) : f p = g (p - 1) := by
    simp only [f, g, section4Mass, section5Rho, ite_eq_right (by omega : ¬p < r),
      ite_eq_right (by omega : p ≠ r), ite_eq_right (by omega : ¬p + 1 < r),
      ite_eq_right (by omega : p + 1 ≠ r), Nat.add_sub_cancel,
      show p - 1 + 1 = p by omega]
  have hpartial : ∀ j, r ≤ j → (∑ p ∈ Finset.range (j + 1), f p) =
      (∑ p ∈ Finset.range j, g p) + δ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have hi : r - 1 + 1 = r := by omega
      have hf := Finset.sum_range_succ f (r - 1)
      have hg := Finset.sum_range_succ g (r - 1)
      rw [hi] at hf hg
      have hprefix : (∑ p ∈ Finset.range (r - 1), f p) = ∑ p ∈ Finset.range (r - 1), g p := by
        exact Finset.sum_congr rfl (fun p hp => hbefore p (by simp only [Finset.mem_range] at hp; omega))
      rw [Finset.sum_range_succ, hf, hprefix, hsplit, hnew, hg]
      dsimp [g, δ]
      rw [hi]
      ring
    | succ j hj ih =>
      rw [Finset.sum_range_succ, ih, hafter (j + 1) (by omega), Nat.add_sub_cancel,
        Finset.sum_range_succ]
      ring
  change (1 / 2) * (∑ p ∈ Finset.range (k + 3), f p) =
    (1 / 2) * (∑ p ∈ Finset.range (k + 2), g p) + _
  rw [hpartial (k + 2) (by omega)]
  dsimp [δ]
  ring

private theorem sum_merge_adjacent (f g : ℕ → ℝ) {n p : ℕ} (hp : p ≤ n)
    (hbefore : ∀ j < p, g j = f j) (hmerge : g p = f p + f (p + 1))
    (hafter : ∀ j, p < j → j ≤ n → g j = f (j + 1)) :
    ∑ j ∈ Finset.range (n + 1), g j = ∑ j ∈ Finset.range (n + 2), f j := by
  induction n with
  | zero =>
    have hp0 : p = 0 := by omega
    subst p
    simpa [Finset.sum_range_succ] using hmerge
  | succ n ih =>
    by_cases hpn : p ≤ n
    · rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        Finset.sum_range_succ (f := g) (n + 1), Finset.sum_range_succ (f := f) (n + 2),
        ih hpn (fun j hpj hj => hafter j hpj (by omega)), hafter (n + 1) (by omega) le_rfl]
    · have hpe : p = n + 1 := by omega
      subst p
      have he : (∑ j ∈ Finset.range (n + 1), g j) = ∑ j ∈ Finset.range (n + 1), f j :=
        Finset.sum_congr rfl (fun j hj => hbefore j (Finset.mem_range.mp hj))
      rw [show n + 1 + 2 = ((n + 1) + 1) + 1 by omega,
        Finset.sum_range_succ (f := g) (n + 1),
        Finset.sum_range_succ (f := f) (n + 1 + 1),
        Finset.sum_range_succ (f := f) (n + 1), he, hmerge]
      ring

theorem schemeCorrection_mergeEqualMass (θ : ℝ → ℝ) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) :
    schemeCorrection θ (s.mergeEqualMass p hp hm) = schemeCorrection θ s := by
  unfold schemeCorrection
  congr 1
  apply sum_merge_adjacent _ _ hp
  · intro j hj
    simp only [RSBScheme.mergeEqualMass, skipLevel, ite_eq_left hj,
      ite_eq_left (show j < p + 1 by omega), ite_eq_left (show j + 1 < p + 1 by omega)]
  · simp only [RSBScheme.mergeEqualMass, skipLevel, lt_self_iff_false, ite_false,
      Nat.lt_succ_self, ite_true, hm]
    ring
  · intro j hj hjk
    simp only [RSBScheme.mergeEqualMass, skipLevel, ite_eq_right (show ¬j < p by omega),
      ite_eq_right (show ¬j < p + 1 by omega), ite_eq_right (show ¬j + 1 < p + 1 by omega)]

end FourPapersCommon
