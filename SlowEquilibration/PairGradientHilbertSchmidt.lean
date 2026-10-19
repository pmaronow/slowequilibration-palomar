-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ObservationCrossBlockOrders

/-! Actual rank-one refinement of the pair tangent-gradient covariance.
Bessel's inequality isolates the single spatial overlap correction from
its m-dimensional transport block, giving the manuscript's sharp orders. -/
@[expose] public section
namespace SlowEquilibration.PairObservationCrossCovariance
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma frameSum_basis {N m : ℕ} (e : Fin m → Vector N) (i : Fin m) :
    frameSum e (EuclideanSpace.basisFun (Fin m) ℝ i)=e i := by
  classical
  simp [frameSum,EuclideanSpace.basisFun_apply,ite_smul,eq_comm]

lemma orthonormal_sum_inner_sq_le {N m : ℕ} (e : Fin m → Vector N)
    (he : Orthonormal ℝ e) (v : Vector N) :
    ∑ i,(inner ℝ (e i) v)^2 ≤ ‖v‖^2 := by
  simpa only [Finset.mem_univ,Finset.sum_const_zero,Finset.sum_ite_irrel,ite_true,
    Real.norm_eq_abs,sq_abs] using he.sum_inner_products_le (s:=Finset.univ) v

lemma normalized_frame_inner_squares {N m : ℕ} (hN : 0 < N)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (v : Vector N) (hv : ‖v‖^2=(N:ℝ)) :
    ∑ i,(inner ℝ (e i) v/Real.sqrt (N:ℝ))^2 ≤ 1 := by
  simp_rw [div_pow]
  rw [← Finset.sum_div,Real.sq_sqrt (Nat.cast_nonneg N)]
  have h:=orthonormal_sum_inner_sq_le e he v
  rw [hv] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg N)).trans_eq (div_self (by positivity))

lemma gradient_cross_basis_entry {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (e f : Fin m → Vector N) (i j : Fin m) :
    (gradientCLM c x e ((gradientCLM c y f).adjoint (EuclideanSpace.basisFun (Fin m) ℝ j))) i=
      firstCovariance c (overlap x y)*inner ℝ (e i) (f j)+
      secondCovariance c (overlap x y)*(inner ℝ (e i) y/Real.sqrt (N:ℝ))*
        (inner ℝ x (f j)/Real.sqrt (N:ℝ)) := by
  have h:=gradient_cross_inner hN c hc x y e f
    (EuclideanSpace.basisFun (Fin m) ℝ i) (EuclideanSpace.basisFun (Fin m) ℝ j)
  dsimp only at h
  rw [frameSum_basis,frameSum_basis,EuclideanSpace.basisFun_inner] at h
  exact h

/-- The actual gradient cross covariance has a transport contribution of
size m F² and one rank-one contribution of size S², with no extra m there. -/
theorem gradient_cross_hilbertSchmidt_le {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    ∑ j,‖((gradientCLM c x e).comp (gradientCLM c y f).adjoint)
      (EuclideanSpace.basisFun (Fin m) ℝ j)‖^2 ≤
      2*(m:ℝ)*(firstCovariance c (overlap x y))^2+2*(secondCovariance c (overlap x y))^2 := by
  let F:=firstCovariance c (overlap x y)
  let S:=secondCovariance c (overlap x y)
  let η:=fun i j : Fin m => inner ℝ (e i) (f j)
  let γ:=fun i : Fin m => inner ℝ (e i) y/Real.sqrt (N:ℝ)
  let δ:=fun j : Fin m => inner ℝ x (f j)/Real.sqrt (N:ℝ)
  have hη : ∑ j,∑ i,(η i j)^2 ≤ (m:ℝ) := by
    calc
      _ ≤ ∑ j : Fin m,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (orthonormal_sum_inner_sq_le e he (f j)).trans_eq (by rw [hf.norm_eq_one j];norm_num)
      _ = _ := by simp
  have hγ : ∑ i,(γ i)^2 ≤ 1 := normalized_frame_inner_squares hN e he y hy
  have hδ : ∑ j,(δ j)^2 ≤ 1 := by
    simpa only [δ,real_inner_comm x] using normalized_frame_inner_squares hN f hf x hx
  have hnorm : (∑ j,‖((gradientCLM c x e).comp (gradientCLM c y f).adjoint)
      (EuclideanSpace.basisFun (Fin m) ℝ j)‖^2)=∑ j,∑ i,(F*η i j+S*γ i*δ j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ContinuousLinearMap.comp_apply,gradient_cross_basis_entry hN c hc,Real.norm_eq_abs,sq_abs]
    rfl
  rw [hnorm]
  calc
    _ ≤ ∑ j,∑ i,(2*F^2*(η i j)^2+2*S^2*(γ i)^2*(δ j)^2) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (F*η i j-S*γ i*δ j)]
    _ = 2*F^2*(∑ j,∑ i,(η i j)^2)+2*S^2*(∑ i,(γ i)^2)*(∑ j,(δ j)^2) := by
      simp_rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum,← Finset.sum_mul]
    _ ≤ 2*F^2*(m:ℝ)+2*S^2*1*1 := by gcongr
    _ = _ := by dsimp only [F,S];ring

/-- Genuine sharp source gradient cross-block square sum, for arbitrary
orthonormal tangent frames and both overlap signs. -/
theorem gradient_cross_hilbertSchmidt_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (_hd : 2 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ∑ j,‖((gradientCLM c x e).comp (gradientCLM c y f).adjoint)
      (EuclideanSpace.basisFun (Fin m) ℝ j)‖^2 ≤
      2*(profileBound c)^2*((m:ℝ)*|overlap x y|^(2*(d-1))+|overlap x y|^(2*(d-2))) := by
  have h:=gradient_cross_hilbertSchmidt_le hN c hc x y hx hy e f he hf
  have hp:=profile_order_common c d hdeg hr
  have hF : (firstCovariance c (overlap x y))^2 ≤ (profileBound c*|overlap x y|^(d-1))^2 := by
    rw [← sq_abs (firstCovariance c (overlap x y))]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity [profileBound_pos c])).mpr hp.2.1
  have hS : (secondCovariance c (overlap x y))^2 ≤ (profileBound c*|overlap x y|^(d-2))^2 := by
    rw [← sq_abs (secondCovariance c (overlap x y))]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity [profileBound_pos c])).mpr hp.2.2.1
  apply h.trans
  calc
    _ ≤ 2*(m:ℝ)*(profileBound c*|overlap x y|^(d-1))^2+
      2*(profileBound c*|overlap x y|^(d-2))^2 := by gcongr
    _ = _ := by rw [mul_pow,mul_pow,← pow_mul,← pow_mul];simp only [Nat.mul_comm];ring

end
end SlowEquilibration.PairObservationCrossCovariance
