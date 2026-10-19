-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalCovarianceTrace
public import SlowEquilibration.GOEPhysicalPrefactors

/-! Exact finite-dimensional bias of the physical GOE covariance-weighted
semicircle resolvent. The square-root formula and true variance normalization
yield an ordinary dimension-inverse estimate throughout the fixed gap ray. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEScaling GOEPhysicalPotential GOEPhysicalPrefactors
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def covarianceResolventRoot (q k : ℝ) : ℝ:=(k-Real.sqrt (k^2-4*q))/2

lemma covariance_semicircle_root {a : ℝ} (ha : 0 < a) (k : ℝ) :
    a*semicircleResolvent (k/a-2)=covarianceResolventRoot (a^2) k := by
  have hs : a*Real.sqrt ((k/a-2)*(4+(k/a-2)))=Real.sqrt (k^2-4*a^2) := by
    calc
      _ = Real.sqrt (a^2)*Real.sqrt ((k/a-2)*(4+(k/a-2))) := by rw [Real.sqrt_sq ha.le]
      _ = Real.sqrt (a^2*((k/a-2)*(4+(k/a-2)))) := (Real.sqrt_mul (sq_nonneg a) _).symm
      _ = _ := by congr 1;field_simp;ring
  unfold semicircleResolvent covarianceResolventRoot
  rw [← mul_div_assoc,mul_sub,hs]
  field_simp
  ring

lemma covarianceResolventRoot_physical {b : ℝ} (hb : 0 < b) (k : ℝ) :
    b*physicalResolvent b k=covarianceResolventRoot b k := by
  have hbS : 0 < Real.sqrt b:=Real.sqrt_pos.mpr hb
  have hc : b*(Real.sqrt b)⁻¹=Real.sqrt b := by
    field_simp
    exact (Real.sq_sqrt hb.le).symm
  unfold physicalResolvent
  rw [← mul_assoc,hc,covariance_semicircle_root hbS,Real.sq_sqrt hb.le]

lemma covarianceResolventRoot_difference {b q g k : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hq : q ≤ b) (hk : 2*Real.sqrt b+g≤k) :
    |covarianceResolventRoot q k-covarianceResolventRoot b k|≤2*(b-q)/g := by
  have hS : 0 < Real.sqrt b:=Real.sqrt_pos.mpr hb
  have hk0 : 0 < k:=by linarith
  have hDb : 0 ≤ k^2-4*b := by nlinarith [Real.sq_sqrt hb.le]
  have hDq : 0 ≤ k^2-4*q := by linarith
  have hroot : g≤Real.sqrt (k^2-4*b) := by
    apply (Real.le_sqrt hg.le hDb).mpr
    nlinarith [Real.sq_sqrt hb.le]
  have hroots : Real.sqrt (k^2-4*b)≤Real.sqrt (k^2-4*q):=Real.sqrt_le_sqrt (by linarith)
  have hDelta : (Real.sqrt (k^2-4*q)-Real.sqrt (k^2-4*b))*g≤4*(b-q) := by
    have hsqb:=Real.sq_sqrt hDb
    have hsqq:=Real.sq_sqrt hDq
    have hdiff0 : 0 ≤ Real.sqrt (k^2-4*q)-Real.sqrt (k^2-4*b):=sub_nonneg.mpr hroots
    have hmul:=mul_le_mul_of_nonneg_left
      (show g≤Real.sqrt (k^2-4*q)+Real.sqrt (k^2-4*b) by linarith [Real.sqrt_nonneg (k^2-4*q)]) hdiff0
    nlinarith
  unfold covarianceResolventRoot
  rw [show (k-Real.sqrt (k^2-4*q))/2-(k-Real.sqrt (k^2-4*b))/2=
    -(Real.sqrt (k^2-4*q)-Real.sqrt (k^2-4*b))/2 by ring,
    abs_div,abs_neg,abs_of_nonneg (sub_nonneg.mpr hroots)]
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (le_div_iff₀ hg).mpr
  nlinarith

/-- Exact finite-a_N target differs from the source b*m_b(k) by at most
2*b*j/(g*N). All true physical normalization factors remain explicit. -/
theorem physical_covariance_target_bias (n j : ℕ) {b g k : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hk : 2*Real.sqrt b+g≤k) :
    |scaleFactor n (n+1+j) b*semicircleResolvent (k/scaleFactor n (n+1+j) b-2)-
      b*physicalResolvent b k| ≤ (2*b*(j:ℝ)/g)/(n+1:ℝ) := by
  let a:=scaleFactor n (n+1+j) b
  have ha : 0 < a:=scaleFactor_pos n (by omega) hb
  have hasq : a^2=b*(n+1:ℝ)/(n+1+j:ℕ):=scaleFactor_square n (by omega) hb.le
  have hle : a^2≤b := by
    rw [hasq]
    apply (div_le_iff₀ (by positivity : 0 < ((n+1+j:ℕ):ℝ))).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hb.le (Nat.cast_nonneg j)]
  rw [covariance_semicircle_root ha,covarianceResolventRoot_physical hb]
  have hroot:=covarianceResolventRoot_difference hb hg hle hk
  have hDiff : b-a^2=b*(j:ℝ)/(n+1+j:ℕ) := by
    rw [hasq]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  rw [hDiff] at hroot
  calc
    _ ≤ _ :=hroot
    _ = (2*b*(j:ℝ)/g)/(n+1+j:ℕ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by simp only [Nat.cast_add,Nat.cast_one];linarith [Nat.cast_nonneg (α:=ℝ) j])

end
end SlowEquilibration.GOEClippedResolvent
