module
public import FourPapersCommon.MixedLocalLeft
public import FourPapersCommon.MixedCurvatureUniform
public import Targets.Section5LocalRight
public import Targets.Section4NeighborFactors

@[expose] public section

/-! Actual mixed local right lambda-slope and constrained-pressure bounds.
The original physical overlap, rather than its variance clock, is optimized. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

 def mixedRightSlope (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (t u : ℝ) : ℝ :=
  section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h r
    (mixedRightSplitVariance ξ s r t u)-u

 theorem section4RightR_mem_Icc_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r≤k+1) (v : ℝ) : section4RightR s β h r v∈Icc (0:ℝ) 1 := by
  rw [←section4RightR_padOneLast s β h hr v]
  exact section4THessianSquare_mem_Icc s.padOneLast β h (by omega) _

 theorem hasDerivWithinAt_mixedRightSlope (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r≤k+1)
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (s.q r) (s.q (r+1))) :
    HasDerivWithinAt (mixedRightSlope ξ s h r t)
      (t*ξ.second u*section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h r
        (mixedRightSplitVariance ξ s r t u)-1)
      (Icc (s.q r) (s.q (r+1))) u := by
  have hmap : MapsTo (mixedRightSplitVariance ξ s r t) (Icc (s.q r) (s.q (r+1)))
    (Icc (0:ℝ) ((mixedBeta ξ)^2*((mixedClockScheme ξ s).q (r+1)-(mixedClockScheme ξ s).q r))) :=
    fun z hz=>mixedRightSplitVariance_mem ξ s hr ht hz
  have hu0 : u∈Icc (-1:ℝ) 1 := ⟨by linarith [s.q_nonneg (p:=r) (by omega),hu.1],
    hu.2.trans (s.q_le_one (by omega))⟩
  have hv : HasDerivAt (mixedRightSplitVariance ξ s r t) (t*ξ.second u) u := by
    change HasDerivAt (fun z=>t*(ξ.first z-ξ.first (s.q r))) (t*ξ.second u) u
    exact ((ξ.hasDerivAt_first_unit hu0).sub_const (ξ.first (s.q r))).const_mul t
  have H:=(hasDerivWithinAt_section4RightQ_all_levels (mixedClockScheme ξ s)
    (mixedBeta ξ) h hr (hmap hu)).comp u hv.hasDerivWithinAt hmap
  convert! H.sub ((hasDerivAt_id u).hasDerivWithinAt) using 1
  ring

 theorem mixedRightSlope_le_local_of_endpoint_curvature (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r≤k+1)
    {t t₀ u e : ℝ} (ht : t∈Icc (0:ℝ) t₀) (ht₀ : t₀<1) (he : 0≤e)
    (hu : u∈Icc (s.q r) (s.q (r+1)))
    (hQ : section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h r 0=s.q r)
    (hR : ξ.second (s.q r)*section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h r 0≤1+e)
    (he_small : e≤(1-t₀)/4)
    (hu_small : mixedLocalSlopeConstant ξ*(u-s.q r)≤(1-t₀)/4) :
    mixedRightSlope ξ s h r t u≤-(1-t₀)/2*(u-s.q r) := by
  have ht1 : t∈Icc (0:ℝ) 1:=⟨ht.1,ht.2.trans ht₀.le⟩
  have hsub : Icc (s.q r) u⊆Icc (s.q r) (s.q (r+1)):=Icc_subset_Icc le_rfl hu.2
  have hzero : (0:ℝ)∈Icc 0 ((mixedBeta ξ)^2*((mixedClockScheme ξ s).q (r+1)-(mixedClockScheme ξ s).q r)) :=
    ⟨le_rfl,(mixedRightSplitVariance_mem ξ s hr ht1 hu).1.trans (mixedRightSplitVariance_mem ξ s hr ht1 hu).2⟩
  have hderiv (z : ℝ) (hz : z∈Icc (s.q r) u) :=
    (hasDerivWithinAt_mixedRightSlope ξ s h hr ht1 (hsub hz)).mono hsub
  have hbound (z : ℝ) (hz : z∈Icc (s.q r) u) :
    t*ξ.second z*section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h r
      (mixedRightSplitVariance ξ s r t z)-1≤-(1-t₀)/2 := by
    let R:=section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h r
    let v:=mixedRightSplitVariance ξ s r t z
    let K:=ξ.jetBound
    have hK : 0≤K:=zero_le_one.trans ξ.jetBound_spec.1
    have hz0 : z∈Icc (0:ℝ) 1:=⟨(s.q_nonneg (by omega)).trans hz.1,
      (hsub hz).2.trans (s.q_le_one (by omega))⟩
    have hq0 : s.q r∈Icc (0:ℝ) 1:=⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
    have hSq : |ξ.second (s.q r)|≤K :=
      (ξ.abs_second_le_at_one (abs_le.mpr ⟨by linarith [hq0.1],hq0.2⟩)).trans ξ.jetBound_spec.2.1
    have hSl:=ξ.second_lipschitz_unit hz0 hq0
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1)] at hSl
    have hv:=mixedRightSplitVariance_mem ξ s hr ht1 (hsub hz)
    have hvle : v≤K*(u-s.q r) := by
      have HF:=ξ.first_lipschitz_unit (r:=z) (q:=s.q r)
        ⟨by linarith [hz0.1],hz0.2⟩ ⟨by linarith [hq0.1],hq0.2⟩
      have hF0 : 0≤ξ.first z-ξ.first (s.q r) := by
        have H:=ξ.first_strictMonoOn.monotoneOn
          ⟨by linarith [hq0.1],hq0.2⟩ ⟨by linarith [hz0.1],hz0.2⟩ hz.1
        linarith
      rw [abs_of_nonneg hF0] at HF
      have HF':=HF.trans (mul_le_mul_of_nonneg_right ξ.jetBound_spec.2.1 (abs_nonneg _))
      rw [abs_of_nonneg (sub_nonneg.mpr hz.1)] at HF'
      have Ht:=mul_le_of_le_one_left hF0 ht1.2
      change t*(ξ.first z-ξ.first (s.q r))≤K*(u-s.q r)
      nlinarith only [Ht,HF',mul_le_mul_of_nonneg_left (show z-s.q r≤u-s.q r by linarith [hz.2]) hK]
    have hRl:=section4RightR_lipschitz_uniform_all_levels (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv hzero
    rw [sub_zero,abs_of_nonneg hv.1] at hRl
    have hRz:=section4RightR_mem_Icc_all_levels (mixedClockScheme ξ s) (mixedBeta ξ) h hr v
    have Hprod : ξ.second z*R v≤ξ.second (s.q r)*R 0+mixedLocalSlopeConstant ξ*(u-s.q r) := by
      have HS:=(abs_le.mp hSl).2
      have HR:=(abs_le.mp hRl).2
      have H1:=mul_le_mul_of_nonneg_left HR (ξ.second_nonneg (s.q r))
      have H2:=mul_le_mul_of_nonneg_right HS hRz.1
      have H3:=mul_le_mul hSq (show (535:ℝ)*v≤535*(K*(u-s.q r)) by linarith only [hvle])
        (mul_nonneg (by norm_num : (0:ℝ)≤535) hv.1) hK
      rw [abs_of_nonneg (ξ.second_nonneg (s.q r))] at H3
      have H4:=mul_le_mul_of_nonneg_left hRz.2 (mul_nonneg hK (sub_nonneg.mpr hz.1))
      have H5:=mul_le_mul_of_nonneg_left (show z-s.q r≤u-s.q r by linarith [hz.2]) hK
      dsimp [mixedLocalSlopeConstant]
      nlinarith only [H1,H2,H3,H4,H5]
    have Hscaled:=mul_le_mul_of_nonneg_left Hprod ht.1
    have Hbase:=mul_le_mul_of_nonneg_left hR ht.1
    have He:=mul_le_of_le_one_left he ht1.2
    have Hlocal:=mul_le_of_le_one_left
      (mul_nonneg (mixedLocalSlopeConstant_nonneg ξ) (sub_nonneg.mpr hu.1)) ht1.2
    nlinarith only [Hscaled,Hbase,He,Hlocal,ht.2,he_small,hu_small]
  have hc : ContinuousOn (mixedRightSlope ξ s h r t) (Icc (s.q r) u) :=
    fun z hz=>(hderiv z hz).continuousWithinAt
  have hd : DifferentiableOn ℝ (mixedRightSlope ξ s h r t) (interior (Icc (s.q r) u)) := by
    rw [interior_Icc]
    exact fun z hz=>((hderiv z ⟨hz.1.le,hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)).differentiableAt.differentiableWithinAt
  have HB : ∀z∈interior (Icc (s.q r) u),deriv (mixedRightSlope ξ s h r t) z≤-(1-t₀)/2 := by
    rw [interior_Icc]
    intro z hz
    rw [((hderiv z ⟨hz.1.le,hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)).deriv]
    exact hbound z ⟨hz.1.le,hz.2.le⟩
  have H:=(convex_Icc (s.q r) u).image_sub_le_mul_sub_of_deriv_le hc hd HB
    (s.q r) ⟨le_rfl,hu.1⟩ u ⟨hu.1,le_rfl⟩ hu.1
  have Hzero : mixedRightSlope ξ s h r t (s.q r)=0 := by
    simp only [mixedRightSlope,mixedRightSplitVariance,sub_self,mul_zero,hQ]
  rwa [Hzero,sub_zero] at H

universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

 theorem mixed_constrainedPhi_local_right_of_endpoint_curvature
    {n k : ℕ} (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {r : ℕ} (hr0 : 1≤r) (hr : r≤k+1)
    {t t₀ u e : ℝ} (ht : t∈Icc (0:ℝ) t₀) (ht₀ : t₀<1) (he : 0≤e)
    (hu : u∈Icc (s.q r) (s.q (r+1))) [Nonempty (AT.ConstrainedPair n u)]
    (hQ : section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h r 0=s.q r)
    (hR : ξ.second (s.q r)*section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h r 0≤1+e)
    (he_small : e≤(1-t₀)/4)
    (hu_small : mixedLocalSlopeConstant ξ*(u-s.q r)≤(1-t₀)/4) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
      2*mixedInterpolationPsi ξ s h t-(1-t₀)^2/8*(u-s.q r)^2 := by
  have Hslope:=mixedRightSlope_le_local_of_endpoint_curvature ξ s h hr ht ht₀ he hu hQ hR he_small hu_small
  have H:=mixed_constrainedPhi_le_two_Psi_sub_right_factor_sq hn ξ s h sk hr0 hr
    ⟨ht.1,ht.2.trans ht₀.le⟩ hu
  have HL:=deriv_section5RightV_zero_eq_Q_all_levels (mixedClockScheme ξ s) (mixedBeta ξ)
    h hr (mixedRightSplitVariance_mem ξ s hr ⟨ht.1,ht.2.trans ht₀.le⟩ hu)
  simp only [mixedClockScheme_m] at HL
  rw [HL] at H
  change _≤2*mixedInterpolationPsi ξ s h t-(mixedRightSlope ξ s h r t u)^2/2 at H
  have Hnonneg : 0≤(1-t₀)/2*(u-s.q r):=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.1)
  have Hneg : (1-t₀)/2*(u-s.q r)≤-mixedRightSlope ξ s h r t u := by linarith only [Hslope]
  have Hsquare:=mul_self_le_mul_self Hnonneg Hneg
  nlinarith only [H,Hsquare]

end FourPapersCommon
