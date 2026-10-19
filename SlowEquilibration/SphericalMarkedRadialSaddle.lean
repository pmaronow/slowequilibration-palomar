-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedStrongConcavity
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual global radial saddle is selected from the literal continuous
coercive complexity, and its existence and uniqueness are proved internally. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalSequentialRegression
open scoped Topology
set_option maxHeartbeats 400000

theorem sourceRadialProfile_continuous (μ : FiniteMixture) (Q e : ℝ) :
    Continuous (sourceRadialProfile μ Q e) := by
  have hscore : Continuous (fun k : ℝ => scoreQuadratic μ Q (scorePairEquiv (e,k))) := by
    simp_rw [source_scoreQuadratic_precision_form]
    fun_prop
  have hpot : Continuous (fun k : ℝ => SemicirclePotential.potential (k/Real.sqrt (Q^2*μ.xi2 Q))) :=
    SemicircleWholeLine.potential_continuous.comp (continuous_id.div_const _)
  change Continuous (fun k : ℝ => 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
    scoreQuadratic μ Q (scorePairEquiv (e,k))/2+SemicirclePotential.potential (k/Real.sqrt (Q^2*μ.xi2 Q)))
  exact (continuous_const.sub (hscore.div_const 2)).add hpot

private theorem continuous_coercive_profile_exists_max (f : ℝ → ℝ) (hf : Continuous f)
    {C a : ℝ} (ha : 0 < a) (hbound : ∀ k : ℝ,f k ≤ C-a*k^2) :
    ∃ m : ℝ,∀ k : ℝ,f k ≤ f m := by
  let R := Real.sqrt ((|C|+|f 0|+1)/a)+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hzero : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith,by linarith⟩
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0,hzero⟩ hf.continuousOn
  refine ⟨m,?_⟩
  intro k
  by_cases hk : k ∈ Icc (-R) R
  · exact hmax hk
  have hkR : R < |k| := by
    apply lt_of_not_ge
    intro hn
    exact hk (abs_le.mp hn)
  have hroot : Real.sqrt ((|C|+|f 0|+1)/a) ≤ |k| := by dsimp [R] at hkR; linarith
  have hsq : (|C|+|f 0|+1)/a ≤ k^2 := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg k)).mpr hroot
    rwa [Real.sq_sqrt (by positivity),sq_abs] at hh
  have hprod := (div_le_iff₀ ha).mp hsq
  have hout : f k ≤ f 0 := by
    have hb := hbound k
    nlinarith [le_abs_self C,neg_le_abs (f 0)]
  exact hout.trans (hmax hzero)

theorem sourceRadialProfile_exists_global_max (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) : ∃ k : ℝ,∀ j : ℝ,sourceRadialProfile μ Q e j ≤ sourceRadialProfile μ Q e k := by
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  apply continuous_coercive_profile_exists_max (C := sourceMarkedCoercivityConstant μ β x Q) (sourceRadialProfile μ Q e)
    (sourceRadialProfile_continuous μ Q e) (show 0 < sourceMarkedLeastCurvature μ Q/8 by positivity)
  intro k
  have hh := sourceMarkedComplexity_global_coercivity μ h hnp e k
  have hp : 0 ≤ sourceMarkedLeastCurvature μ Q/8*e^2 := by positivity
  nlinarith

irreducible_def sourceRadialSaddle (μ : FiniteMixture) (Q e : ℝ) : ℝ :=
  Classical.epsilon (fun k : ℝ => ∀ j : ℝ,sourceRadialProfile μ Q e j ≤ sourceRadialProfile μ Q e k)

theorem sourceRadialSaddle_global_max (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e j : ℝ) : sourceRadialProfile μ Q e j ≤ sourceRadialProfile μ Q e (sourceRadialSaddle μ Q e) := by
  rw [sourceRadialSaddle_def]
  exact Classical.epsilon_spec (sourceRadialProfile_exists_global_max μ h hnp e) j

/-- No maximizer is supplied as input to the saddle definition. Every
actual global maximizer agrees with the unique selected true radial saddle. -/
theorem sourceRadialSaddle_eq_of_global_max (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e m : ℝ) (hm : ∀ j : ℝ,sourceRadialProfile μ Q e j ≤ sourceRadialProfile μ Q e m) :
    m=sourceRadialSaddle μ Q e := by
  let k := sourceRadialSaddle μ Q e
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  have hConcave := sourceMarkedComplexity_strongly_concave μ h.overlap_range.1 hnp
  have hMid := hConcave.2 (mem_univ (e,m)) (mem_univ (e,k))
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have hPair : (1/2 : ℝ) • (e,m)+(1/2 : ℝ) • (e,k)=(e,(m+k)/2) := by
    ext <;> simp only [Prod.smul_mk,smul_eq_mul,Prod.mk_add_mk] <;> ring
  rw [hPair] at hMid
  change (1/2 : ℝ)*(sourceRadialProfile μ Q e m+sourceMarkedLeastCurvature μ Q/2*(e^2+m^2))+
    (1/2 : ℝ)*(sourceRadialProfile μ Q e k+sourceMarkedLeastCurvature μ Q/2*(e^2+k^2)) ≤
    sourceRadialProfile μ Q e ((m+k)/2)+sourceMarkedLeastCurvature μ Q/2*(e^2+((m+k)/2)^2) at hMid
  have hkm := hm k
  have hmk := sourceRadialSaddle_global_max μ h hnp e m
  have hmiddle := hm ((m+k)/2)
  by_contra hne
  have hp : 0 < sourceMarkedLeastCurvature μ Q*(m-k)^2 :=
    mul_pos hκ (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  nlinarith

theorem sourceRadialSaddle_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    sourceRadialSaddle μ Q (markE μ β x Q)=markK μ β Q := by
  apply (sourceRadialSaddle_eq_of_global_max μ h hnp (markE μ β x Q) (markK μ β Q) ?_).symm
  intro j
  have hLoss := sourceMarkedComplexity_global_loss μ h hnp (markE μ β x Q) j
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  rw [sourceContact_radialProfile_zero μ h hnp]
  simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_add] at hLoss
  have hp : 0 ≤ sourceMarkedLeastCurvature μ Q*(j-markK μ β Q)^2/2 := by positivity
  linarith

theorem sourceRadialSaddle_stationary_of_above_edge (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < sourceRadialSaddle μ Q e) :
    sourceRadialProfileDerivative μ Q e (sourceRadialSaddle μ Q e)=0 := by
  have hmax : IsLocalMax (sourceRadialProfile μ Q e) (sourceRadialSaddle μ Q e) :=
    Filter.Eventually.of_forall (sourceRadialSaddle_global_max μ h hnp e)
  exact hmax.hasDerivAt_eq_zero (sourceRadialProfile_hasDerivAt μ h.overlap_range.1 e _ hk)

end SlowEquilibration.SphericalMarkedWindows
