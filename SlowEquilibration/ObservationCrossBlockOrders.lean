-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ObservationCrossBlocks
public import SlowEquilibration.PairObservationNormBounds

/-! Sharp dimension-free orders of the actual cross observation blocks,
used by the two-point Gaussian density factorization. -/
@[expose] public section
namespace SlowEquilibration.PairObservationCrossCovariance
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma score_form_le {a b d e A B C L : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hd : |d| ≤ 1) (he : |e| ≤ 1)
    (hA : |A| ≤ L) (hB : |B| ≤ L) (hC : |C| ≤ 2*L) :
    |a*d*A+a*e*B+b*d*B+b*e*C| ≤ 5*L := by
  have h1:=abs_triple_le ha hd hA
  have h2:=abs_triple_le ha he hB
  have h3:=abs_triple_le hb hd hB
  have h4:=abs_triple_le hb he hC
  grw [abs_add_le,abs_add_le,abs_add_le]
  linarith

lemma unit_score_coordinates (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖=1) :
    |u 0| ≤ 1 ∧ |u 1| ≤ 1 := by
  exact ⟨by simpa only [Real.norm_eq_abs,hu] using PiLp.norm_apply_le u (0:Fin 2),
    by simpa only [Real.norm_eq_abs,hu] using PiLp.norm_apply_le u (1:Fin 2)⟩

/-- Extensive normalized score cross covariance has the genuine order d. -/
theorem score_cross_order {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 2 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hr : |overlap x y| ≤ 1) :
    ‖(normalizedScore c x).comp (normalizedScore c y).adjoint‖ ≤
      5*profileBound c * |overlap x y|^d := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (normalizedScore c x ((normalizedScore c y).adjoint v)) u ≤ _
  rw [real_inner_comm,score_cross_inner hN c hc]
  have huc:=unit_score_coordinates u hu
  have hvc:=unit_score_coordinates v hv
  have hp:=normalized_score_profile_orders c hd hdeg hr
  have hbound:=score_form_le huc.1 huc.2 hvc.1 hvc.2 hp.1 hp.2.1 (by simpa only [mul_assoc] using hp.2.2)
  exact (le_abs_self _).trans (by convert hbound using 1;ring)

lemma first_overlap_second_order {P : ℕ} (c : Degree P → ℝ) {d : ℕ}
    (hd : 2 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val) {r : ℝ} (hr : |r| ≤ 1) :
    |firstCovariance c r+r*secondCovariance c r| ≤ 2*profileBound c * |r|^(d-1) := by
  have hp:=profile_order_common c d hdeg hr
  have hS : |r*secondCovariance c r| ≤ profileBound c * |r|^(d-1) := by
    rw [abs_mul]
    calc
      _ ≤ |r| * (profileBound c * |r|^(d-2)) := mul_le_mul_of_nonneg_left hp.2.2.1 (abs_nonneg r)
      _ = _ := by rw [mul_left_comm,← pow_succ',show d-2+1=d-1 by omega]
  exact (abs_add_le _ _).trans (by linarith [hp.2.1])

/-- Actual score/gradient cross covariance has order d−1, uniformly over
N and over the full tangent-gradient frame. -/
theorem score_gradient_cross_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 2 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ‖(normalizedScore c x).comp (gradientCLM c y f).adjoint‖ ≤
      3*profileBound c * |overlap x y|^(d-1) := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (normalizedScore c x ((gradientCLM c y f).adjoint v)) u ≤ _
  rw [real_inner_comm,score_gradient_cross_inner hN c hc]
  have huc:=unit_score_coordinates u hu
  have hV : ‖frameSum f v‖ ≤ 1 := by rw [frameSum_norm f hf,hv]
  have hgamma:=normalized_inner_le_one hN x hx (frameSum f v) hV
  have hp:=(profile_order_common c d hdeg hr).2.1
  have hmix:=first_overlap_second_order c hd hdeg hr
  have h1 : |u 0*firstCovariance c (overlap x y)*(inner ℝ x (frameSum f v)/Real.sqrt (N:ℝ))| ≤
      profileBound c * |overlap x y|^(d-1) := by
    simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le huc.1 hgamma hp
  have h2 : |u 1*(firstCovariance c (overlap x y)+overlap x y*secondCovariance c (overlap x y))*
      (inner ℝ x (frameSum f v)/Real.sqrt (N:ℝ))| ≤ 2*profileBound c * |overlap x y|^(d-1) := by
    simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le huc.2 hgamma hmix
  exact (le_abs_self _).trans ((abs_add_le _ _).trans (by linarith))

/-- The actual gradient/gradient cross covariance has order d−2. The
normalization of the rank-one term cancels its two sqrt N factors. -/
theorem gradient_cross_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 2 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ‖(gradientCLM c x e).comp (gradientCLM c y f).adjoint‖ ≤
      2*profileBound c * |overlap x y|^(d-2) := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (gradientCLM c x e ((gradientCLM c y f).adjoint v)) u ≤ _
  rw [real_inner_comm,gradient_cross_inner hN c hc]
  let U:=frameSum e u
  let V:=frameSum f v
  have hU : ‖U‖=1 := (frameSum_norm e he u).trans hu
  have hV : ‖V‖=1 := (frameSum_norm f hf v).trans hv
  have hdelta : |inner ℝ U y/Real.sqrt (N:ℝ)| ≤ 1 := by
    rw [real_inner_comm]
    exact normalized_inner_le_one hN y hy U hU.le
  have hgamma:=normalized_inner_le_one hN x hx V hV.le
  have hzeta : |inner ℝ U V| ≤ 1 := by simpa only [hU,hV,mul_one] using abs_real_inner_le_norm U V
  have hp:=profile_order_common c d hdeg hr
  have hF : |firstCovariance c (overlap x y)| ≤ profileBound c * |overlap x y|^(d-2) :=
    hp.2.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (abs_nonneg _) hr (by omega : d-2 ≤ d-1)) (profileBound_pos c).le)
  have h1 : |firstCovariance c (overlap x y)*inner ℝ U V| ≤ profileBound c * |overlap x y|^(d-2) := by
    simpa [mul_comm] using abs_triple_le (by norm_num : |(1:ℝ)| ≤ 1) hzeta hF
  have h2 : |secondCovariance c (overlap x y)*(inner ℝ U y/Real.sqrt (N:ℝ))*
      (inner ℝ x V/Real.sqrt (N:ℝ))| ≤ profileBound c * |overlap x y|^(d-2) := by
    simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le hdelta hgamma hp.2.2.1
  exact (le_abs_self _).trans ((abs_add_le _ _).trans (by linarith))

end
end SlowEquilibration.PairObservationCrossCovariance
