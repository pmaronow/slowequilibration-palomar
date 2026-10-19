-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationNormBounds

/-! Exact active-degree vanishing orders of the actual finite covariance
profiles. These bounds preserve the powers needed for local pair density
factorization, rather than replacing them with first-order estimates. -/
@[expose] public section
namespace SlowEquilibration.SphericalTwoPointCovariance
noncomputable section
open SphericalModel SphericalGaussianJet PairObservationNormBounds
open scoped BigOperators
set_option maxHeartbeats 400000

lemma polynomial_order_bound {ι : Type*} [Fintype ι] (a : ι → ℝ) (e : ι → ℕ)
    (k : ℕ) (hvan : ∀ i,a i≠0 → k ≤ e i) {r : ℝ} (hr : |r| ≤ 1) :
    |∑ i,a i*r^(e i)| ≤ (∑ i,|a i|) * |r|^k := by
  calc
    _ ≤ ∑ i,|a i*r^(e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,|a i| * |r|^k := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : a i=0
      · simp [hz]
      · rw [abs_mul,abs_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (abs_nonneg r) hr (hvan i hz)) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The exact four genuine covariance orders d,d−1,d−2,d−3. -/
theorem profile_order_bounds {P : ℕ} (c : Degree P → ℝ) (d : ℕ)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ valueProfileBound c * |r|^d ∧
    |firstCovariance c r| ≤ firstProfileBound c * |r|^(d-1) ∧
    |secondCovariance c r| ≤ secondProfileBound c * |r|^(d-2) ∧
    |thirdCovariance c r| ≤ thirdProfileBound c * |r|^(d-3) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact polynomial_order_bound c (fun p => p.val.val) d hdeg hr
  · exact polynomial_order_bound (fun p => c p*(p.val.val:ℝ)) (fun p => p.val.val-1) (d-1)
      (fun p hp => by
        have hcp : c p≠0 := by intro hz;simp [hz] at hp
        have h:=hdeg p hcp;omega) hr
  · exact polynomial_order_bound (fun p => c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)) (fun p => p.val.val-2) (d-2)
      (fun p hp => by
        have hcp : c p≠0 := by intro hz;simp [hz] at hp
        have h:=hdeg p hcp;omega) hr
  · exact polynomial_order_bound (fun p => c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)*((p.val.val:ℝ)-2))
      (fun p => p.val.val-3) (d-3)
      (fun p hp => by
        have hcp : c p≠0 := by intro hz;simp [hz] at hp
        have h:=hdeg p hcp;omega) hr

/-- All exact powers can use one fixed finite coefficient constant. -/
theorem profile_order_common {P : ℕ} (c : Degree P → ℝ) (d : ℕ)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ profileBound c * |r|^d ∧
    |firstCovariance c r| ≤ profileBound c * |r|^(d-1) ∧
    |secondCovariance c r| ≤ profileBound c * |r|^(d-2) ∧
    |thirdCovariance c r| ≤ profileBound c * |r|^(d-3) := by
  have h:=profile_order_bounds c d hdeg hr
  have hn0 : 0 ≤ valueProfileBound c := by unfold valueProfileBound;positivity
  have hn1 : 0 ≤ firstProfileBound c := by unfold firstProfileBound;positivity
  have hn2 : 0 ≤ secondProfileBound c := by unfold secondProfileBound;positivity
  have hn3 : 0 ≤ thirdProfileBound c := by unfold thirdProfileBound;positivity
  unfold profileBound
  exact ⟨h.1.trans (by nlinarith [pow_nonneg (abs_nonneg r) d]),
    h.2.1.trans (by nlinarith [pow_nonneg (abs_nonneg r) (d-1)]),
    h.2.2.1.trans (by nlinarith [pow_nonneg (abs_nonneg r) (d-2)]),
    h.2.2.2.trans (by nlinarith [pow_nonneg (abs_nonneg r) (d-3)])⟩

/-- The mixed score cross block has genuine order d, since its derivative
profiles occur with the actual extra overlap factors. -/
theorem normalized_score_profile_orders {P : ℕ} (c : Degree P → ℝ) {d : ℕ}
    (hd : 2 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ profileBound c * |r|^d ∧
    |r*firstCovariance c r| ≤ profileBound c * |r|^d ∧
    |r*firstCovariance c r+r^2*secondCovariance c r| ≤ 2*profileBound c * |r|^d := by
  have hp:=profile_order_common c d hdeg hr
  have hF : |r*firstCovariance c r| ≤ profileBound c * |r|^d := by
    rw [abs_mul]
    calc
      _ ≤ |r| * (profileBound c * |r|^(d-1)) := mul_le_mul_of_nonneg_left hp.2.1 (abs_nonneg r)
      _ = _ := by rw [mul_left_comm,← pow_succ',show d-1+1=d by omega]
  have hS : |r^2*secondCovariance c r| ≤ profileBound c * |r|^d := by
    rw [abs_mul,abs_pow]
    calc
      _ ≤ |r|^2*(profileBound c * |r|^(d-2)) := mul_le_mul_of_nonneg_left hp.2.2.1 (sq_nonneg _)
      _ = _ := by rw [mul_left_comm,← pow_add,show 2+(d-2)=d by omega]
  exact ⟨hp.1,hF,(abs_add_le _ _).trans (by linarith)⟩

end
end SlowEquilibration.SphericalTwoPointCovariance
