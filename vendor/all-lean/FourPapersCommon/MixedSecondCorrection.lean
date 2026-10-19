module
public import FourPapersCommon.SchemeCorrectionAlgebra
public import FourPapersCommon.MixedSecondInterpolationAlgebra
public import Targets.RightInterpolationAlgebra

@[expose] public section

/-! Exact physical θ corrections in the two genuine mixed paths. -/
noncomputable section
open Real
open SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem insertedCorrection_sum (θ : ℝ → ℝ) {k : ℕ} (s : RSBScheme k)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ) :
    (∑ p ∈ Finset.range (k + 3), section4Mass s r m p *
      (θ (section5Rho s r u (p + 1)) - θ (section5Rho s r u p))) =
    (∑ p ∈ Finset.range (k + 2), s.m p * (θ (s.q (p + 1)) - θ (s.q p))) +
      (m - s.m (r - 1)) * (θ (s.q r) - θ u) := by
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
  exact hpartial (k + 2) (by omega)


theorem mixedPairCascadeCorrection_eq_split (ξ : AdmissibleEvenMixture)
    (m ρ : ℕ → ℝ) (κ τ : ℕ) :
    mixedPairCascadeCorrection ξ m ρ (fun l => ρ (min l τ)) κ =
      ∑ p ∈ Finset.range (κ + 1), (if p < τ then (2 : ℝ) else 1) * m p *
        (ξ.correction (ρ (p + 1)) - ξ.correction (ρ p)) := by
  apply Finset.sum_congr rfl
  intro p _
  unfold mixedPairTrialEnergy
  by_cases hp : p < τ
  · simp only [ite_eq_left hp, min_eq_left (by omega : p ≤ τ), min_eq_left (by omega : p + 1 ≤ τ)]
    ring
  · simp only [ite_eq_right hp, min_eq_right (by omega : τ ≤ p), min_eq_right (by omega : τ ≤ p + 1)]
    ring

theorem mixedLeftPairCorrection_eq (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (u m : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r u)
      (fun l => section5Rho s r u (min l r)) (k + 2) =
      2 * mixedSchemeCorrection ξ s +
        (m - s.m (r - 1)) * (ξ.correction (s.q r) - ξ.correction u) := by
  rw [mixedPairCascadeCorrection_eq_split]
  have hcoeff (p : ℕ) :
      (if p < r then (2 : ℝ) else 1) * section5Mass s r m p = section4Mass s r m p := by
    unfold section5Mass section4Mass
    split_ifs <;> ring
  simp_rw [hcoeff]
  rw [insertedCorrection_sum ξ.correction s r hr0 hr m u,
    mixedSchemeCorrection_eq_schemeCorrection, schemeCorrection]
  ring

theorem rightInsertedCorrection_sum (θ : ℝ → ℝ) {k : ℕ} (s : RSBScheme k)
    (r : ℕ) (hr : r ≤ k + 1) (m u : ℝ) :
    (∑ p ∈ Finset.range (k + 3),
      (if p < r + 1 then (2 : ℝ) else 1) * section5RightMass s r m p *
      (θ (section5RightRho s r u (p + 1)) - θ (section5RightRho s r u p))) =
    (∑ p ∈ Finset.range (k + 2), s.m p * (θ (s.q (p + 1)) - θ (s.q p))) +
      (m - s.m r) * (θ u - θ (s.q r)) := by
  let f := fun p => (if p < r + 1 then (2 : ℝ) else 1) * section5RightMass s r m p *
    (θ (section5RightRho s r u (p + 1)) - θ (section5RightRho s r u p))
  let g := fun p => s.m p * (θ (s.q (p + 1)) - θ (s.q p))
  let δ := (m - s.m r) * (θ u - θ (s.q r))
  have hbefore (p : ℕ) (hp : p < r) : f p = g p := by
    simp only [f, g, section5RightMass, section5Mass, section5RightRho, section5Rho,
      ite_eq_left hp, ite_eq_left (by omega : p < r + 1),
      ite_eq_left (by omega : p + 1 < r + 1)]
    ring
  have hsplit : f r = m * (θ u - θ (s.q r)) := by
    simp only [f, section5RightMass, section5Mass, section5RightRho, section5Rho,
      ite_eq_left (by omega : r < r + 1), lt_self_iff_false, ite_false, ite_true]
    ring
  have hnew : f (r + 1) = s.m r * (θ (s.q (r + 1)) - θ u) := by
    simp only [f, section5RightMass, section5Mass, section5RightRho, section5Rho,
      lt_self_iff_false, ite_false, ite_true,
      ite_eq_right (by omega : ¬r + 1 < r), ite_eq_right (by omega : r + 1 ≠ r),
      ite_eq_right (by omega : ¬r + 1 + 1 < r + 1),
      ite_eq_right (by omega : r + 1 + 1 ≠ r + 1), Nat.add_sub_cancel]
    ring
  have hafter (p : ℕ) (hp : r + 1 < p) : f p = g (p - 1) := by
    simp only [f, g, section5RightMass, section5Mass, section5RightRho, section5Rho,
      ite_eq_right (by omega : ¬p < r + 1), ite_eq_right (by omega : ¬p < r),
      ite_eq_right (by omega : p ≠ r), ite_eq_right (by omega : p ≠ r + 1),
      ite_eq_right (by omega : ¬p + 1 < r + 1), ite_eq_right (by omega : p + 1 ≠ r + 1),
      Nat.add_sub_cancel, show p - 1 + 1 = p by omega, one_mul]
  have hpartial : ∀ j, r + 1 ≤ j → (∑ p ∈ Finset.range (j + 1), f p) =
      (∑ p ∈ Finset.range j, g p) + δ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have hprefix : (∑ p ∈ Finset.range r, f p) = ∑ p ∈ Finset.range r, g p :=
        Finset.sum_congr rfl (fun p hp => hbefore p (Finset.mem_range.mp hp))
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hprefix, hsplit, hnew,
        Finset.sum_range_succ]
      dsimp [g, δ]
      ring
    | succ j hj ih =>
      rw [Finset.sum_range_succ, ih, hafter (j + 1) (by omega), Nat.add_sub_cancel,
        Finset.sum_range_succ]
      ring
  exact hpartial (k + 2) (by omega)

theorem mixedRightPairCorrection_eq (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (u m : ℝ) {r : ℕ} (hr : r ≤ k + 1) :
    mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r u)
      (fun l => section5RightRho s r u (min l (r + 1))) (k + 2) =
      2 * mixedSchemeCorrection ξ s +
        (m - s.m r) * (ξ.correction u - ξ.correction (s.q r)) := by
  rw [mixedPairCascadeCorrection_eq_split,
    rightInsertedCorrection_sum ξ.correction s r hr m u,
    mixedSchemeCorrection_eq_schemeCorrection, schemeCorrection]
  ring

end FourPapersCommon
