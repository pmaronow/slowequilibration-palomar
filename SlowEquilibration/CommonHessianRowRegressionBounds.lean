-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianRowQuadraticVariance
public import SlowEquilibration.PairHessianMean
public import SlowEquilibration.CovarianceProfileOrders

/-! Dimension-free actual common border-row regression coupling and mean
bounds. The vector estimate retains the common projection contraction. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianObservationCoercivity GaussianCovarianceRepresentation
open NormalizedPairObservations HessianObservationCovariance SphericalTwoPointCovariance
open PairObservationNormBounds PairHessianMean
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

lemma synthesis_frame_norm_le {N m : ℕ} (e : Fin m → Vector N) (he : Orthonormal ℝ e) :
    ‖synthesis e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [synthesis_apply]
  change ‖frameSum e u‖ ≤ 1*‖u‖
  rw [frameSum_norm e he,one_mul]

lemma common_row_mixed_coupling {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y v : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) (w : MixedObservationSpace k) :
    commonRowCLM c x e v ((singleMixedObservation c y f).adjoint w)=
      (secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ v y) • (synthesis e).adjoint (frameSum f w.snd) := by
  apply PiLp.ext
  intro i
  rw [commonRowCLM_apply,hessian_mixed_coupling hN c hc hdeg]
  simp only [htany,mul_zero,zero_mul,add_zero,zero_add,PiLp.smul_apply,
    smul_eq_mul,synthesis_adjoint_apply]
  ring

/-- True common row/normalized mixed observation coupling is
O(|overlap|^(d−2)/sqrt N), without a sqrt(m) loss. -/
theorem common_row_mixed_cross_norm {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hv : ‖v‖=1)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) (hf : Orthonormal ℝ f) (hr : |overlap x y| ≤ 1) :
    ‖(commonRowCLM c x e v).comp (singleMixedObservation c y f).adjoint‖ ≤
      profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by
  have hL:=(profileBound_pos c).le
  let s:=Real.sqrt (N:ℝ)
  have hs : 0 < s:=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hs2 : s^2=(N:ℝ):=Real.sq_sqrt (Nat.cast_nonneg N)
  have hi : |inner ℝ v y| ≤ s := by
    have hh:=(abs_real_inner_le_norm v y)
    have hys : ‖y‖=s := (sq_eq_sq₀ (norm_nonneg _) hs.le).mp (hy.trans hs2.symm)
    simpa only [hv,hys,one_mul] using hh
  have hS:=(profile_order_common c d hdeg hr).2.2.1
  have hcoeff : |secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ v y| ≤
      profileBound c*|overlap x y|^(d-2)/s := by
    rw [abs_mul,abs_div,abs_of_pos (show 0 < (N:ℝ) from Nat.cast_pos.mpr hN)]
    calc
      _ ≤ (profileBound c*|overlap x y|^(d-2)/(N:ℝ))*s := by gcongr
      _ = _ := by rw [← hs2];field_simp
  have hproj : ‖(synthesis e).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using synthesis_frame_norm_le e he
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [profileBound_pos c])
  intro w
  rw [ContinuousLinearMap.comp_apply,common_row_mixed_coupling hN c hc (fun p hp=>le_trans hd (hdeg p hp)) x y v e htany f w]
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ v y| *‖frameSum f w.snd‖ :=
      mul_le_mul_of_nonneg_left (((synthesis e).adjoint.le_opNorm _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hproj)) (abs_nonneg _)
    _ ≤ (profileBound c*|overlap x y|^(d-2)/s)*‖w‖ := by
      rw [frameSum_norm f hf]
      exact mul_le_mul hcoeff (WithLp.norm_snd_le _ w) (norm_nonneg _) (by positivity [profileBound_pos c])

lemma common_row_own_mixed_cross_zero {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0)
    (hv : inner ℝ v x=0) (f : Fin k → Vector N) :
    (commonRowCLM c x e v).comp (singleMixedObservation c x f).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply PiLp.ext
  intro i
  change commonRowCLM c x e v ((singleMixedObservation c x f).adjoint w) i=0
  rw [commonRowCLM_apply]
  exact own_mixed_hessian_zero hN c hc hdeg x (e i) v (htan i) hv f w

/-- Genuine pair coupling bound, retaining the zero own-point block. -/
theorem common_row_pair_mixed_cross_norm {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1) :
    ‖(commonRowCLM c x e v).comp
      (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)).adjoint‖ ≤
      profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by
  have hother:=common_row_mixed_cross_norm hN c hc hd hdeg x y v hy hv e he htany g hg hr
  have hown:=common_row_own_mixed_cross_zero hN c hc (fun p hp=>le_trans hd (hdeg p hp)) x v e htanx hvtan f
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [profileBound_pos c])
  intro w
  rw [ContinuousLinearMap.comp_apply,pairHilbert_adjoint,map_add]
  have hzero:=congrArg (fun T:MixedObservationSpace k→L[ℝ]EuclideanSpace ℝ (Fin m)=>T w.fst) hown
  change commonRowCLM c x e v ((singleMixedObservation c x f).adjoint w.fst)=0 at hzero
  rw [hzero,zero_add]
  exact (((commonRowCLM c x e v).comp (singleMixedObservation c y g).adjoint).le_opNorm w.snd).trans
    (mul_le_mul hother (WithLp.norm_snd_le _ w) (norm_nonneg _) (by positivity [profileBound_pos c]))

/-- Actual full-vector conditional row mean, on extensive bounded targets,
has order |overlap|^(d−2) without a dimension factor. -/
theorem common_row_pair_mixed_lift_norm {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1)
    {δ M : ℝ} (hδ : 0 < δ) (_hM : 0 ≤ M)
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k)) (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) :
    ‖commonRowCLM c x e v (lift (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)) w)‖ ≤
      (profileBound c*M/δ)*|overlap x y|^(d-2) := by
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  have hcross:=common_row_pair_mixed_cross_norm hN c hc hd hdeg x y v hy hv hvtan e he htanx htany f g hg hr
  have hs : 0 < Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  change ‖((commonRowCLM c x e v).comp A.adjoint) ((gram A).inverse w)‖ ≤ _
  calc
    _ ≤ ‖(commonRowCLM c x e v).comp A.adjoint‖*‖(gram A).inverse w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ))*((1/δ)*‖w‖) := by
      exact mul_le_mul hcross (((gram A).inverse.le_opNorm w).trans
        (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))) (norm_nonneg _) (by positivity [profileBound_pos c])
    _ ≤ (profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ))*((1/δ)*(M*Real.sqrt (N:ℝ))) := by
      gcongr
      positivity [profileBound_pos c]
    _=_ := by field_simp

/-- Actual regression covariance correction has operator norm
O(|overlap|^(2d−4)/N), from the genuine row/observation cross norm. -/
theorem common_row_pair_residual_gram_norm {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1)
    {δ : ℝ} (_hδ : 0 < δ)
    (hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1/δ) :
    let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
    ‖gram ((commonRowCLM c x e v).comp (residual A))-gram (commonRowCLM c x e v)‖ ≤
      profileBound c^2/((N:ℝ)*δ)*|overlap x y|^(2*(d-2)) := by
  dsimp only
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  have hcross:=common_row_pair_mixed_cross_norm hN c hc hd hdeg x y v hy hv hvtan e he htanx htany f g hg hr
  have hK : 0 ≤ profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by positivity [profileBound_pos c]
  calc
    _ ≤ ‖(commonRowCLM c x e v).comp A.adjoint‖^2*‖(gram A).inverse‖ :=
      residual_gram_difference_bound A hA (commonRowCLM c x e v)
    _ ≤ (profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ))^2*(1/δ) :=
      mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hK).mpr hcross) hinv (norm_nonneg _) (sq_nonneg _)
    _=_ := by
      rw [div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),← pow_mul,Nat.mul_comm (d-2) 2]
      ring

end
end SlowEquilibration.SphericalCommonHessianRegression
