-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationNormBounds
public import SlowEquilibration.NormalizedObservationCoercivity

/-! Actual dimension-independent small-overlap nonsingularity, with the
constants selected before every dimension and pair of sphere points. -/
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

lemma mixed_unit_coordinate_bounds {m : ℕ} (u : MixedObservationSpace m) (hu : ‖u‖=1) :
    |u.fst 0| ≤ 1 ∧ |u.fst 1| ≤ 1 ∧ ‖u.snd‖ ≤ 1 := by
  have hf : ‖u.fst‖ ≤ 1 := (WithLp.norm_fst_le _ u).trans_eq hu
  have h0:= (PiLp.norm_apply_le u.fst (0:Fin 2)).trans hf
  have h1:= (PiLp.norm_apply_le u.fst (1:Fin 2)).trans hf
  exact ⟨by simpa only [Real.norm_eq_abs] using h0,
    by simpa only [Real.norm_eq_abs] using h1,(WithLp.norm_snd_le _ u).trans_eq hu⟩

lemma mixed_cross_unit_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (u v : MixedObservationSpace m) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hr : |overlap x y| ≤ 1) :
    |inner ℝ u (singleMixedObservation c x e ((singleMixedObservation c y f).adjoint v))| ≤
      13*profileBound c*|overlap x y| := by
  let U:=frameSum e u.snd
  let V:=frameSum f v.snd
  let r:=overlap x y
  let s:=Real.sqrt (N:ℝ)
  have huc:=mixed_unit_coordinate_bounds u hu
  have hvc:=mixed_unit_coordinate_bounds v hv
  have hU : ‖U‖ ≤ 1 := by rw [frameSum_norm e he];exact huc.2.2
  have hV : ‖V‖ ≤ 1 := by rw [frameSum_norm f hf];exact hvc.2.2
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
  have hb:=mixed_form_bound huc.1 huc.2.1 hvc.1 hvc.2.1 hr
    hgamma hdelta hzeta hp.1 hp.2.1 hp.2.2.1
  have hform := mixed_cross_inner hN c hc x y e f u v
  dsimp only at hform
  have hs : s^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : s≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have hN0 : (N:ℝ)≠0 := by positivity
  have heq : inner ℝ u (singleMixedObservation c x e ((singleMixedObservation c y f).adjoint v))=
      u.fst 0*v.fst 0*covariancePolynomial c r+
      u.fst 0*v.fst 1*(r*firstCovariance c r)+
      u.fst 1*v.fst 0*(r*firstCovariance c r)+
      u.fst 1*v.fst 1*(r*firstCovariance c r+r^2*secondCovariance c r)+
      u.fst 0*firstCovariance c r*(inner ℝ x V/s)+
      u.fst 1*(firstCovariance c r+r*secondCovariance c r)*(inner ℝ x V/s)+
      v.fst 0*firstCovariance c r*(inner ℝ U y/s)+
      v.fst 1*(firstCovariance c r+r*secondCovariance c r)*(inner ℝ U y/s)+
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

/-- The actual cross Gram has an operator bound with no dimension factor. -/
theorem mixed_cross_opNorm {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ‖(singleMixedObservation c x e).comp (singleMixedObservation c y f).adjoint‖ ≤
      13*profileBound c*|overlap x y| := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (singleMixedObservation c x e ((singleMixedObservation c y f).adjoint v)) u ≤ _
  rw [real_inner_comm]
  exact (le_abs_self _).trans (mixed_cross_unit_bound hN c hc hdeg x y hx hy e f he hf u v hu hv hr)

lemma center_degree_four {μ : FiniteMixture} (hμ : 4 ≤ μ.minDegree) (Q : ℝ) :
    ∀ p,centerCoefficients (mixtureCoefficients μ) Q p≠0 → 4 ≤ p.val.val := by
  intro p hp
  have hc : μ.coeff p.val.val≠0 := by
    intro hz
    apply hp
    simp [centerCoefficients,mixtureCoefficients,hz]
  exact hμ.trans (μ.degree_bounds (Finsupp.mem_support_iff.mpr hc)).1

/-- Actual mixed pair nondegeneracy holds uniformly in N on a genuine
small-overlap neighborhood. Both constants precede the dimension and targets. -/
theorem uniform_mixed_pair_nondegenerate (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 δ : ℝ,0 < ρ0 ∧ 0 < δ ∧ ∀ (N m : ℕ) (_hN : 0 < N)
      (x y : Vector N),‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) →
      |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)
      CoerciveObservation A δ ∧ Surjective A ∧ ‖(gram A).inverse‖ ≤ 1/δ := by
  obtain ⟨α,hα,hbase⟩:=uniform_mixed_coercivity μ hQ hnp
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
  have hcross : ‖(singleMixedObservation c x e).comp (singleMixedObservation c y f).adjoint‖ ≤ α/2 :=
    (mixed_cross_opNorm hN c (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le)
      (center_degree_four hdeg Q) x y hx hy e f he hf hr1).trans (by nlinarith)
  have hAx:=hbase N m hN x hx e he htanx
  have hAy:=hbase N m hN y hy f hf htany
  have hpair:=pair_coercive _ _ hα hAx hAy hcross
  exact ⟨hpair,observation_surjective _ (by positivity) hpair,
    gram_inverse_norm_le _ (by positivity) hpair⟩

end
end SlowEquilibration.PairObservationSmallOverlap
