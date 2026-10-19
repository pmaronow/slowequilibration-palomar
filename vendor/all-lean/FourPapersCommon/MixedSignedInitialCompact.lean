module
public import FourPapersCommon.MixedSignedInitialOrigin
public import FourPapersCommon.MixedInterleavedCompact

@[expose] public section

/-! Fixed-trial signed scalar witnesses and closed compact negative-initial
margins. Positive frozen-field variance supplies the zero-overlap endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

 theorem continuous_retainedSignedInitial_variances {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    Continuous (fun p:(ℝ×ℝ×ℝ)×ℝ×(ℝ×ℝ) =>
      section5RetainedSignedInitialCascade s β p.1.2.1 p.1.2.2 p.1.1 p.2.1 p.2.2) := by
  let F := fun (p:ℝ×ℝ×ℝ) ell xy => section5SignedInitialPrefix s β p.1 ell xy
  let D := fun (p:ℝ×ℝ×ℝ) ell xy => section5SignedInitialPrefixD s β p.1 ell xy
  have HG : GTFrame.GoodFam (section5SignedInitialPrefix s β) (section5SignedInitialPrefixD s β) :=
    splitScalarCascade_good (fun j => section5Mass s 1 0 (k+2-j))
      (fun j => section5Variance s β 1 (k+2-j))
      (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
      (fun j => section5Variance_continuous s β 1 (k+2-j)) (k+2) (k+2)
  have HF : GTFrame.GoodFam F D := by
    constructor
    · exact HG.contF.comp (show Continuous (fun p:(ℝ×ℝ×ℝ)×ℝ×(ℝ×ℝ) => (p.1.1,p.2.1,p.2.2)) by fun_prop)
    · exact HG.contD.comp (show Continuous (fun p:(ℝ×ℝ×ℝ)×ℝ×(ℝ×ℝ) => (p.1.1,p.2.1,p.2.2)) by fun_prop)
    · exact fun p ell xy => HG.hasDeriv p.1 ell xy
    · exact fun p ell xy yz => HG.lipx p.1 ell xy yz
    · exact fun p ell xy => HG.bddD p.1 ell xy
  have H1 := finiteStep_good HF (m:=0) le_rfl
    (a:=fun p:ℝ×ℝ×ℝ => Real.sqrt p.2.1) (b:=fun p:ℝ×ℝ×ℝ => Real.sqrt p.2.1)
    (by fun_prop) (by fun_prop)
  have H2 := finiteStep_good H1 (m:=0) le_rfl
    (a:=fun p:ℝ×ℝ×ℝ => Real.sqrt p.2.2) (b:=fun p:ℝ×ℝ×ℝ => -Real.sqrt p.2.2)
    (by fun_prop) (by fun_prop)
  convert H2.contF using 1
  funext p
  simp [section5RetainedSignedInitialCascade,section5RetainedInitialPrefix,
    GTFrame.finiteStep,GTFrame.step0,F]

 def mixedSignedInitialComparisonDeficit (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h v ell : ℝ) (p:ℝ×ℝ) : ℝ :=
    2*parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k+2) h-
      section5RetainedSignedInitialV (mixedClockScheme ξ s) (mixedBeta ξ) h
        (p.1*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock v)))
        ((1-p.1)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
        (p.1*((mixedBeta ξ)^2*(-ξ.clock v))) ell+
      ell*p.2-p.1*ξ.tangentRemainder p.2 v

 theorem continuousOn_mixedSignedInitialComparisonDeficit
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h v ell : ℝ)
    {S : Set (ℝ×ℝ)} (hS : ∀p∈S,p.2∈Icc (-1:ℝ) 1) :
    ContinuousOn (mixedSignedInitialComparisonDeficit ξ s h v ell) S := by
  have HV := (continuous_retainedSignedInitial_variances (mixedClockScheme ξ s) (mixedBeta ξ)).comp
    (show Continuous (fun p:ℝ×ℝ =>
      ((p.1*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock v)),
       (1-p.1)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1),
       p.1*((mixedBeta ξ)^2*(-ξ.clock v))),ell,(h,h))) by fun_prop)
  have HR : ContinuousOn (fun p:ℝ×ℝ => ξ.tangentRemainder p.2 v) S := by
    unfold AdmissibleEvenMixture.tangentRemainder
    exact ((ξ.continuousOn_value.comp continuous_snd.continuousOn hS).sub continuousOn_const).sub
      (continuousOn_const.mul (continuous_snd.continuousOn.sub continuousOn_const))
  unfold mixedSignedInitialComparisonDeficit section5RetainedSignedInitialV
  exact ((continuousOn_const.sub HV.continuousOn).add
    (continuousOn_const.mul continuous_snd.continuousOn)).sub (continuous_fst.continuousOn.mul HR)

 theorem exists_mixedSignedInitialComparison_compact_witnesses
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hunit : ∀p∈S,p.2∈Icc (-1:ℝ) 1)
    (hpos : ∀p∈S,∃v∈Icc (-s.q 1) 0,∃ell,0 < mixedSignedInitialComparisonDeficit ξ s h v ell p) :
    ∃delta>(0:ℝ),∀p∈S,∃v∈Icc (-s.q 1) 0,∃ell,delta ≤ mixedSignedInitialComparisonDeficit ξ s h v ell p := by
  let I := {v:ℝ // v∈Icc (-s.q 1) 0}×ℝ
  let f := fun i:I => mixedSignedInitialComparisonDeficit ξ s h i.1.1 i.2
  have hc (i:I) : ContinuousOn (f i) S :=
    continuousOn_mixedSignedInitialComparisonDeficit ξ s h i.1.1 i.2 hunit
  have hp : ∀p∈S,∃i:I,0<f i p := by
    intro p hp
    obtain ⟨v,hv,ell,H⟩ := hpos p hp
    exact ⟨(⟨v,hv⟩,ell),H⟩
  obtain ⟨delta,hd,Hd⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨delta,hd,?_⟩
  intro p hp
  obtain ⟨i,hi⟩ := Hd p hp
  exact ⟨i.1.1,i.1.2,i.2,hi⟩

universe u
 theorem mixed_constrainedPhi_le_signedInitialComparison
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {t u v ell : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (-1:ℝ) 0) (hv : v∈Icc (-s.q 1) 0)
    (hatt : ∃σ τ:Config n,overlap n σ τ=u) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u ≤
      2*mixedInterpolationPsi ξ s h t-mixedSignedInitialComparisonDeficit ξ s h v ell (t,u) := by
  obtain ⟨σ,τ,H⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ,τ),H⟩⟩
  have HH := mixedSignedInitial_constrainedPhi_le hn ξ s h sk ht hu hv ell
  simp only [mixedClockScheme_q] at HH
  dsimp [mixedInterpolationPsi,mixedSignedInitialComparisonDeficit]
  linarith only [HH]

 theorem exists_mixed_constrainedPhi_compact_signedInitial_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (ht : ∀p∈S,p.1∈Icc (0:ℝ) 1)
    (hu : ∀p∈S,p.2∈Icc (-1:ℝ) 0)
    (hpos : ∀p∈S,∃v∈Icc (-s.q 1) 0,∃ell,0 < mixedSignedInitialComparisonDeficit ξ s h v ell p) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  obtain ⟨delta,hd,Hd⟩ := exists_mixedSignedInitialComparison_compact_witnesses ξ s h hS
    (fun p hp => ⟨(hu p hp).1,(hu p hp).2.trans zero_le_one⟩) hpos
  refine ⟨delta,hd,?_⟩
  intro Ω _ _ p hp n hn sk hatt
  obtain ⟨v,hv,ell,Hell⟩ := Hd p hp
  have HB := mixed_constrainedPhi_le_signedInitialComparison hn ξ s h sk
    (ell:=ell) (ht p hp) (hu p hp) hv hatt
  exact HB.trans (by linarith only [Hell])

 theorem exists_mixedSignedInitialComparison_witness_of_near_minimum
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : s.m 0<s.m 1) (hq1 : 0<s.q 1) (hright : s.q 1<s.q 2 ∨ s.q 1=1)
    {t t₀ u : ℝ} (ht : t∈Icc (0:ℝ) t₀) (ht₀ : t₀<1) (hu : u∈Icc (-s.q 1) 0)
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h+ε)
    (hsmall : mixedLocalLeftConstant ξ*ε^(1/6:ℝ) ≤ 1-t₀) :
    ∃v∈Icc (-s.q 1) 0,∃ell,0 < mixedSignedInitialComparisonDeficit ξ s h v ell (t,u) := by
  by_cases hu0 : u=0
  · have hqc : 0<(mixedClockScheme ξ s).q 1 := by
      have H := ξ.clock_strictMonoOn (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
        ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hq1
      simpa only [ξ.clock_zero,mixedClockScheme_q] using H
    obtain ⟨ell,HL⟩ := retainedSignedInitial_origin_scalar_witness (mixedClockScheme ξ s)
      (mixedBeta ξ) h (mixedBeta_ne_zero ξ) hqc ⟨ht.1,ht.2.trans_lt ht₀⟩
    refine ⟨0,⟨by linarith,le_rfl⟩,ell,?_⟩
    simpa only [mixedSignedInitialComparisonDeficit,hu0,ξ.clock_zero,add_zero,neg_zero,
      mul_zero,sub_zero,tangentRemainder_self] using HL
  · obtain ⟨e,he,hes,HR⟩ := mixed_initial_curvature_data_of_near_minimum ξ s h ε
      hm hq1 hright ht₀ hmin hnear hsmall
    obtain ⟨ell,_,HL⟩ := mixedSignedInitial_scalar_gain_bounded ξ s h ht ht₀ hu he hes HR
    refine ⟨u,hu,ell,?_⟩
    have HP : 0<(1-t₀)^2/8*u^2 := mul_pos
      (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num)) (sq_pos_of_ne_zero hu0)
    simp only [mixedSignedInitialComparisonDeficit,tangentRemainder_self,mul_zero,sub_zero]
    linarith only [HL,HP]

 theorem exists_mixed_constrainedPhi_compact_negative_initial_interval_gap
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : s.m 0<s.m 1) (hq1 : 0<s.q 1) (hright : s.q 1<s.q 2 ∨ s.q 1=1)
    {t₀ : ℝ} (ht₀ : t₀<1) {S : Set (ℝ×ℝ)} (hS : IsCompact S)
    (ht : ∀p∈S,p.1∈Icc (0:ℝ) t₀) (hu : ∀p∈S,p.2∈Icc (-s.q 1) 0)
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h+ε)
    (hsmall : mixedLocalLeftConstant ξ*ε^(1/6:ℝ) ≤ 1-t₀) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  apply exists_mixed_constrainedPhi_compact_signedInitial_gap_all_spaces ξ s h hS
    (fun p hp => ⟨(ht p hp).1,(ht p hp).2.trans ht₀.le⟩)
    (fun p hp => ⟨by linarith [(hu p hp).1,s.q_le_one (p:=1) (by omega)],(hu p hp).2⟩)
  exact fun p hp => exists_mixedSignedInitialComparison_witness_of_near_minimum ξ s h ε
    hm hq1 hright (ht p hp) ht₀ (hu p hp) hmin hnear hsmall

end FourPapersCommon
