-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationSmallOverlap

/-! Proper value-only pair conditioning, including pure mixtures. -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationCrossCovariance PairObservationNormBounds
open NormalizedObservationCoercivity GaussianObservationCoercivity GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma value_unit_coordinate_bounds {m : ℕ} (u : ValueObservationSpace m) (hu : ‖u‖=1) :
    |u.fst| ≤ 1 ∧ ‖u.snd‖ ≤ 1 := by
  exact ⟨by simpa only [Real.norm_eq_abs] using (WithLp.norm_fst_le _ u).trans_eq hu,
    (WithLp.norm_snd_le _ u).trans_eq hu⟩

lemma value_cross_unit_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (u v : ValueObservationSpace m) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hr : |overlap x y| ≤ 1) :
    |inner ℝ u (singleValueObservation c x e ((singleValueObservation c y f).adjoint v))| ≤
      13*profileBound c*|overlap x y| := by
  let U:=frameSum e u.snd
  let V:=frameSum f v.snd
  let r:=overlap x y
  let s:=Real.sqrt (N:ℝ)
  have huc:=value_unit_coordinate_bounds u hu
  have hvc:=value_unit_coordinate_bounds v hv
  have hU : ‖U‖ ≤ 1 := by rw [frameSum_norm e he];exact huc.2
  have hV : ‖V‖ ≤ 1 := by rw [frameSum_norm f hf];exact hvc.2
  have hgamma : |inner ℝ x V/s| ≤ 1 := normalized_inner_le_one hN x hx V hV
  have hdelta : |inner ℝ U y/s| ≤ 1 := by
    rw [real_inner_comm]
    exact normalized_inner_le_one hN y hy U hU
  have hzeta : |inner ℝ U V| ≤ 1 := by
    calc
      _ ≤ ‖U‖*‖V‖ := abs_real_inner_le_norm _ _
      _ ≤ 1*1 := by gcongr
      _ = 1 := by ring
  have hp:=profiles_le_common c hdeg hr
  have hb:=mixed_form_bound huc.1 (by norm_num : |(0:ℝ)| ≤ 1)
    hvc.1 (by norm_num : |(0:ℝ)| ≤ 1) hr hgamma hdelta hzeta hp.1 hp.2.1 hp.2.2.1
  simp only [zero_mul,mul_zero,add_zero] at hb
  have hform := value_cross_inner hN c hc x y e f u v
  dsimp only at hform
  have heq : inner ℝ u (singleValueObservation c x e ((singleValueObservation c y f).adjoint v))=
      u.fst*v.fst*covariancePolynomial c r+
      u.fst*firstCovariance c r*(inner ℝ x V/s)+
      v.fst*firstCovariance c r*(inner ℝ U y/s)+
      firstCovariance c r*inner ℝ U V+
      secondCovariance c r*(inner ℝ U y/s)*(inner ℝ x V/s) := by
    rw [hform]
    dsimp only [U,V,r,s]
    field_simp
    rw [← Real.sq_sqrt (Nat.cast_nonneg N)]
    simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    ring
  rw [heq]
  convert hb using 1; ring

theorem value_cross_opNorm {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ‖(singleValueObservation c x e).comp (singleValueObservation c y f).adjoint‖ ≤
      13*profileBound c*|overlap x y| := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (singleValueObservation c x e ((singleValueObservation c y f).adjoint v)) u ≤ _
  rw [real_inner_comm]
  exact (le_abs_self _).trans (value_cross_unit_bound hN c hc hdeg x y hx hy e f he hf u v hu hv hr)

/-- Proper pure pair observations are genuinely nondegenerate uniformly in
N and overlap, with no impossible independent radial target. -/
theorem uniform_value_pair_nondegenerate (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 δ : ℝ,0 < ρ0 ∧ 0 < δ ∧ ∀ (N m : ℕ) (_hN : 0 < N)
      (x y : Vector N),‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) →
      |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)
      CoerciveObservation A δ ∧ Surjective A ∧ ‖(gram A).inverse‖ ≤ 1/δ := by
  obtain ⟨α,hα,hbase⟩:=uniform_value_coercivity μ hQ
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  have hL : 0 < L := profileBound_pos c
  let ρ0:=min 1 (α/(26*L))
  have hρ0 : 0 < ρ0 := lt_min (by norm_num) (by positivity)
  refine ⟨ρ0,α/2,hρ0,by positivity,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hr
  have hr1 : |overlap x y| ≤ 1 := hr.trans (min_le_left _ _)
  have hrα : 26*L*|overlap x y| ≤ α := by
    have hh:=hr.trans (min_le_right _ _)
    have hh':= (le_div_iff₀ (by positivity : 0 < 26*L)).mp hh
    nlinarith
  have hcross : ‖(singleValueObservation c x e).comp (singleValueObservation c y f).adjoint‖ ≤ α/2 :=
    (value_cross_opNorm hN c (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le)
      (center_degree_four hdeg Q) x y hx hy e f he hf hr1).trans (by nlinarith)
  have hAx:=hbase N m hN x hx e he htanx
  have hAy:=hbase N m hN y hy f hf htany
  have hpair:=pair_coercive _ _ hα hAx hAy hcross
  exact ⟨hpair,observation_surjective _ (by positivity) hpair,
    gram_inverse_norm_le _ (by positivity) hpair⟩

end
end SlowEquilibration.PairObservationSmallOverlap
