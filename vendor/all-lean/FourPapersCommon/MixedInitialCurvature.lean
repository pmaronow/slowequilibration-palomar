module
public import FourPapersCommon.MixedTerminalStationarity
public import FourPapersCommon.MixtureJetBounds
public import Targets.Section4HessianRegularity
public import Targets.Section4HessianUniform
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! The short initial-overlap curvature bound from genuine stationarity.
No division by the mixture variance or its curvature at zero is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem variance_curvature_baseline_bound {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1) :
    section4THessianSquare s β h r 0*(β^2*(s.q r-s.q (r-1)))  ≤ 
      section4TVarianceQ s β h r (s.m (r-1)) 0+535*(β^2*(s.q r-s.q (r-1)))^2 := by
  let v := β^2*(s.q r-s.q (r-1))
  have hmono : s.q (r-1) ≤ s.q r := by
    simpa only [Nat.sub_add_cancel hr0] using s.q_mono (r-1) (by omega)
  have hv : 0 ≤ v := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hmono)
  let Q := section4TVarianceQ s β h r (s.m (r-1))
  let R := section4THessianSquare s β h r
  have hc : ContinuousOn Q (Icc (0 : ℝ) v) :=
    continuousOn_section4TVarianceQ_variance s β h hr0 hr
      ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩
  have hd : DifferentiableOn ℝ Q (interior (Icc (0 : ℝ) v)) := by
    intro z hz
    rw [interior_Icc] at hz
    exact (hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr hz).differentiableAt.differentiableWithinAt
  have hb : ∀ z∈interior (Icc (0 : ℝ) v),deriv Q z  ≤  -R 0+535*v := by
    intro z hz
    rw [interior_Icc] at hz
    rw [(hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr hz).deriv]
    have HL := section4THessianSquare_lipschitz_uniform s β h hr0 hr
      (v := 0) (w := z) ⟨le_rfl,hv⟩ ⟨hz.1.le,hz.2.le⟩
    have ha : |0-z|=z := by rw [zero_sub,abs_neg,abs_of_nonneg hz.1.le]
    rw [ha] at HL
    have HH := (le_abs_self (R 0-R z)).trans HL
    change R 0-R z ≤ 535*z at HH
    have Hz : 535*z ≤ 535*v := mul_le_mul_of_nonneg_left hz.2.le (by norm_num)
    linarith
  have H := (convex_Icc (0 : ℝ) v).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 ⟨le_rfl,hv⟩ v ⟨hv,le_rfl⟩ hv
  have H0 := (section4TVarianceQ_mem_Icc s β h r
    (m := s.m (r-1)) ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩ v).1
  change 0 ≤ Q v at H0
  change R 0*v ≤ Q 0+535*v^2
  nlinarith

theorem mixture_first_le_jetBound_mul (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q∈Icc (0 : ℝ) 1) : ξ.first q ≤ ξ.jetBound*q := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx=>(ξ.hasDerivAt_first_unit
      (show x∈Icc (-1 : ℝ) 1 from ⟨by linarith [hx.1],hx.2⟩)).hasDerivWithinAt)
    (fun x hx=>by
      rw [Real.norm_eq_abs]
      exact (ξ.abs_second_le_at_one (by rw [abs_of_nonneg hx.1]; exact hx.2)).trans ξ.jetBound_spec.2.1)
    (convex_Icc (0 : ℝ) 1) (show (0 : ℝ)∈Icc 0 1 by norm_num) hq
  rw [ξ.first_zero,sub_zero,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hq.1] at H
  exact (le_abs_self _).trans H

theorem mixture_initial_linear_error_bound (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q∈Icc (0 : ℝ) 1) : q*ξ.second q-ξ.jetBound*q^2 ≤ ξ.first q := by
  let f : ℝ → ℝ := fun x=>ξ.first x-x*ξ.second q
  have hd (x : ℝ) (hx : x∈Icc (0 : ℝ) q) : HasDerivAt f (ξ.second x-ξ.second q) x := by
    simpa only [id_eq,one_mul] using
      (ξ.hasDerivAt_first_unit ⟨by linarith [hx.1],hx.2.trans hq.2⟩).fun_sub
        ((hasDerivAt_id x).mul_const (ξ.second q))
  have hc : ContinuousOn f (Icc (0 : ℝ) q) := fun x hx=>(hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) q)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hd x ⟨hx.1.le,hx.2.le⟩).differentiableAt.differentiableWithinAt
  have hl : ∀ x∈interior (Icc (0 : ℝ) q),-ξ.jetBound*q ≤ deriv f x := by
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x ⟨hx.1.le,hx.2.le⟩).deriv]
    have H := ξ.second_lipschitz_unit (show x∈Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2.le.trans hq.2⟩) hq
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2.le)] at H
    have HK : 0 ≤ ξ.jetBound := le_trans (by norm_num) ξ.jetBound_spec.1
    have Habs : -|ξ.second x-ξ.second q| ≤ ξ.second x-ξ.second q := neg_abs_le _
    have HX : ξ.jetBound*(q-x) ≤ ξ.jetBound*q :=
      mul_le_mul_of_nonneg_left (by linarith [hx.1]) HK
    linarith
  have H := (convex_Icc (0 : ℝ) q).mul_sub_le_image_sub_of_le_deriv hc hdiff hl
    0 ⟨le_rfl,hq.1⟩ q ⟨hq.1,le_rfl⟩ hq.1
  dsimp only [f] at H
  rw [ξ.first_zero,zero_mul,sub_zero,sub_zero] at H
  nlinarith

theorem mixed_initial_endpointQ_eq_of_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1=1)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s)  ≤ 
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h 1 (s.m 0) 0=s.q 1 := by
  by_cases hk : 1 ≤ k
  · apply mixed_endpointQ_eq_overlap_of_min_nonterminal ξ s h (r := 1) le_rfl hk
      (by simpa only [Nat.sub_self] using hm)
      (Or.inl (by simpa only [Nat.sub_self,s.q_zero] using hq)) hright hmin
  · have hk0 : k=0 := by omega
    subst k
    exact mixed_endpointQ_eq_overlap_of_min_terminal ξ s h
      (by simpa only [s.m_top] using hm) (Or.inl (by simpa only [s.q_zero] using hq)) hmin

def mixedInitialCurvatureConstant (ξ : AdmissibleEvenMixture) : ℝ :=
  ξ.jetBound+535*ξ.jetBound^2

theorem mixed_initial_curvature_bound (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1=1)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s)  ≤ 
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    ξ.second (s.q 1)*section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0-1  ≤ 
      mixedInitialCurvatureConstant ξ*s.q 1 := by
  let q := s.q 1
  let R := section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0
  let K := ξ.jetBound
  let v := ξ.first q
  have hqmem : q∈Icc (0 : ℝ) 1 := ⟨hq.le,s.q_le_one (by omega)⟩
  have HK : 0 ≤ K := le_trans (by norm_num) ξ.jetBound_spec.1
  have HR : R∈Icc (0 : ℝ) 1 := section4THessianSquare_mem_Icc
    (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) (by omega) 0
  have hvEq : (mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1-(mixedClockScheme ξ s).q 0)=v := by
    rw [mixedClockScheme_variance ξ s 0]
    simp only [s.q_zero,ξ.first_zero,sub_zero]
    rfl
  have HH := variance_curvature_baseline_bound (mixedClockScheme ξ s) (mixedBeta ξ) h
    (r := 1) le_rfl (by omega)
  simp only [Nat.sub_self,mixedClockScheme_m] at HH
  rw [hvEq,mixed_initial_endpointQ_eq_of_min ξ s h hm hq hright hmin] at HH
  change R*v ≤ q+535*v^2 at HH
  have hv0 : 0 ≤ v := by
    have H := ξ.first_strictMonoOn.monotoneOn
      (show (0 : ℝ)∈Icc (-1 : ℝ) 1 by norm_num)
      (show q∈Icc (-1 : ℝ) 1 from ⟨by linarith [hqmem.1],hqmem.2⟩) hqmem.1
    simpa only [ξ.first_zero] using H
  have HV : v ≤ K*q := mixture_first_le_jetBound_mul ξ hqmem
  have HVsq : v^2 ≤ K^2*q^2 := by
    have H := (sq_le_sq₀ hv0 (mul_nonneg HK hqmem.1)).mpr HV
    simpa only [mul_pow] using H
  have Hlin := mul_le_mul_of_nonneg_right (mixture_initial_linear_error_bound ξ hqmem) HR.1
  change (q*ξ.second q-K*q^2)*R ≤ v*R at Hlin
  have Herr := mul_le_mul_of_nonneg_left HR.2 (mul_nonneg HK (sq_nonneg q))
  change K*q^2*R ≤ K*q^2*1 at Herr
  have Hfinal : q*(ξ.second q*R-1) ≤ q*((K+535*K^2)*q) := by
    nlinarith [Hlin,Herr,HH,HVsq]
  exact le_of_mul_le_mul_left Hfinal hq

end FourPapersCommon
