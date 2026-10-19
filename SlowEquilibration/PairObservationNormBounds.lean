-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationCrossCovariance

/-! Dimension-independent norm bounds for the actual normalized pair Gram. -/
@[expose] public section
namespace SlowEquilibration.PairObservationNormBounds
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationCrossCovariance
open scoped RealInnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def profileBound {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  1+valueProfileBound c+firstProfileBound c+secondProfileBound c+thirdProfileBound c

lemma profileBound_pos {P : ℕ} (c : Degree P → ℝ) : 0 < profileBound c := by
  unfold profileBound valueProfileBound firstProfileBound secondProfileBound thirdProfileBound
  positivity

lemma profiles_le_common {P : ℕ} (c : Degree P → ℝ)
    (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ profileBound c*|r| ∧
    |firstCovariance c r| ≤ profileBound c*|r| ∧
    |secondCovariance c r| ≤ profileBound c*|r| ∧
    |thirdCovariance c r| ≤ profileBound c*|r| := by
  have h:=profile_bounds c hdeg hr
  have hn0 : 0 ≤ valueProfileBound c := by unfold valueProfileBound;positivity
  have hn1 : 0 ≤ firstProfileBound c := by unfold firstProfileBound;positivity
  have hn2 : 0 ≤ secondProfileBound c := by unfold secondProfileBound;positivity
  have hn3 : 0 ≤ thirdProfileBound c := by unfold thirdProfileBound;positivity
  unfold profileBound
  exact ⟨h.1.trans (by nlinarith [abs_nonneg r]),
    h.2.1.trans (by nlinarith [abs_nonneg r]),
    h.2.2.1.trans (by nlinarith [abs_nonneg r]),
    h.2.2.2.trans (by nlinarith [abs_nonneg r])⟩

lemma abs_triple_le {a b p L : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hp : |p| ≤ L) :
    |a*b*p| ≤ L := by
  rw [abs_mul,abs_mul]
  calc
    _ ≤ 1*1*L := by gcongr
    _ = L := by ring

/-- An elementary finite bound, with the true ten terms of the pair form. -/
lemma mixed_form_bound {a b d e A B C r s t z L : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hd : |d| ≤ 1) (he : |e| ≤ 1)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) (ht : |t| ≤ 1) (hz : |z| ≤ 1)
    (hA : |A| ≤ L) (hB : |B| ≤ L) (hC : |C| ≤ L) :
    |a*d*A+a*e*(r*B)+b*d*(r*B)+b*e*(r*B+r^2*C)+
      a*B*s+b*(B+r*C)*s+d*B*t+e*(B+r*C)*t+B*z+C*t*s| ≤ 13*L := by
  have hL : 0 ≤ L := (abs_nonneg A).trans hA
  have hrB : |r*B| ≤ L := by simpa using abs_triple_le hr (by norm_num : |(1:ℝ)| ≤ 1) hB
  have hrC : |r*C| ≤ L := by simpa using abs_triple_le hr (by norm_num : |(1:ℝ)| ≤ 1) hC
  have hr2 : |r^2| ≤ 1 := by rw [abs_pow];exact pow_le_one₀ (abs_nonneg r) hr
  have hr2C : |r^2*C| ≤ L := by simpa using abs_triple_le hr2 (by norm_num : |(1:ℝ)| ≤ 1) hC
  have hmix : |B+r*C| ≤ 2*L := (abs_add_le _ _).trans (by linarith)
  have hrad : |r*B+r^2*C| ≤ 2*L := (abs_add_le _ _).trans (by linarith)
  have h1:=abs_triple_le ha hd hA
  have h2:=abs_triple_le ha he hrB
  have h3:=abs_triple_le hb hd hrB
  have h4:=abs_triple_le hb he hrad
  have h5 : |a*B*s| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le ha hs hB
  have h6 : |b*(B+r*C)*s| ≤ 2*L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le hb hs hmix
  have h7 : |d*B*t| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le hd ht hB
  have h8 : |e*(B+r*C)*t| ≤ 2*L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le he ht hmix
  have h9 : |B*z| ≤ L := by simpa [mul_comm] using abs_triple_le (by norm_num : |(1:ℝ)| ≤ 1) hz hB
  have h10 : |C*t*s| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le ht hs hC
  grw [abs_add_le,abs_add_le,abs_add_le,abs_add_le,abs_add_le,
    abs_add_le,abs_add_le,abs_add_le,abs_add_le]
  linarith

lemma norm_eq_sqrt_dimension {N : ℕ} (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    ‖x‖=Real.sqrt (N:ℝ) := by
  rw [← hx,Real.sqrt_sq (norm_nonneg x)]

lemma normalized_inner_le_one {N : ℕ} (hN : 0 < N) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (V : Vector N) (hV : ‖V‖ ≤ 1) :
    |inner ℝ x V/Real.sqrt (N:ℝ)| ≤ 1 := by
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mpr
  calc
    _ ≤ ‖x‖*‖V‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (N:ℝ)*1 := by rw [norm_eq_sqrt_dimension x hx];gcongr
    _ = _ := by ring

end
end SlowEquilibration.PairObservationNormBounds
