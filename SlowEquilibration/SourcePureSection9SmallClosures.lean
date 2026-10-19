-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePurePCCountsLiteral
public import SlowEquilibration.SourcePureCaptureMaximumUpper
public import SlowEquilibration.SourcePureCaptureLiteralConsumer
public import SlowEquilibration.SphericalPureOriginalConditionalBandFubini
public import SlowEquilibration.ReplicaBandExpectedUpper
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! Literal Section 9 closures: tightness of the original pure maximum
about the logarithmic center, the full-width replicated-band limsup bound,
and the conditional cap depth bound in every positive dimension.
These conclusions use the actual original tensor field and sphere law. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureSection9SmallClosures

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate PureStationarity TwoAtomStationarity
open SourcePureCaptureFixedCapEstimates SphericalPureOriginalConditionalBandFubini
open LiteratureSubagPhysicalDefinitions ReplicaBandExpectedUpper
open SphericalPureCapSourceScalars
open SphericalForm
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual posterior mean of the original pure cap partition. Taking
`Q = 1` conditions the original field itself at value `H`, with zero gradient. -/
def capPosteriorMean (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) (β H a : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp alpha halpha
  ∫ J, partitionOn β (field (mixtureCoefficients μ) J)
    (overlapRegion u (Ico a 1))
    ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) 1) u hu
      (H / (n+1 : ℕ))

/-- The depth clause of `prop:pc-laplace`, for every positive dimension,
including dimensions two and three; no coarea-density endpoint is used. -/
theorem pure_cap_posterior_mean_depth_all_dimensions
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ))
    {β a H v : ℝ} (hβ : 0 < β) (ha : a ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    capPosteriorMean n p hp alpha halpha u hu β (H-v) a ≤
      Real.exp (-β*a^p*v) * capPosteriorMean n p hp alpha halpha u hu β H a := by
  have hmean (H : ℝ) : capPosteriorMean n p hp alpha halpha u hu β H a =
      ∫ w in overlapRegion u (Ico a 1),
        originalPureMeanProfile n p alpha β H u w ∂sphereLaw (n+1) := by
    simpa only [capPosteriorMean, Real.sqrt_one, one_pow, one_mul] using
      pure_original_conditioned_band_mean_sphere n p hp alpha halpha
        (Q := 1) (by norm_num) u hu β H (Ico a 1) measurableSet_Ico
  rw [hmean (H-v), hmean H, ← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_sphere_of_continuous (by omega)
      (originalPureMeanProfile_continuous n p alpha β (H-v) u)).restrict
  · exact ((integrable_sphere_of_continuous (by omega)
      (originalPureMeanProfile_continuous n p alpha β H u)).const_mul _).restrict
  · filter_upwards [ae_restrict_mem (overlapRegion_measurable u measurableSet_Ico)]
      with w hw
    have ht : a ≤ overlap u w := by simpa only [overlap, real_inner_comm] using hw.1
    have hpow : a^p ≤ (overlap u w)^p := pow_le_pow_left₀ ha.1.le ht p
    unfold originalPureMeanProfile
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hβ.le hv)]

private theorem real_random_variable_tail {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : X → ℝ) (hf : Measurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ P.real {x | L < |f x|} ≤ ε := by
  let A (j : ℕ) := {x | (j : ℝ) < |f x|}
  have hm : ∀ j, MeasurableSet (A j) := fun j =>
    measurableSet_lt measurable_const hf.abs
  have hanti : Antitone A := by
    intro i j hij x hx
    exact lt_of_le_of_lt (Nat.cast_le.mpr hij) (show (j : ℝ) < |f x| from hx)
  have hempty : (⋂ j, A j) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨j,hj⟩ := exists_nat_gt |f x|
    exact (not_lt_of_ge hj.le) (mem_iInter.mp hx j)
  have hlim : Tendsto (fun j => P.real (A j)) atTop (𝓝 (0 : ℝ)) := by
    have hh := tendsto_measure_iInter_atTop (μ := P)
      (fun j => (hm j).nullMeasurableSet) hanti ⟨0,measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hh
    exact ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _) |>.mpr hh
  obtain ⟨j,hj,hsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  exact ⟨j,by exact_mod_cast (show 0 < j by omega),hsmall.le⟩

private theorem pure_maximum_eventual_tightness
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | L < |sourceSphereMaximum n
          (FiniteMixture.pure p (by omega) 1 (by positivity)) 1 J-
            pureSourceCenter p hp n|} ≤ ε := by
  classical
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K (n : ℕ) (R : ℝ) := physicalEnergyWindow (n+3)
    (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-R)
      (sourcePureAnalyticCenter (n+3) E (β*x)+R)) univ
  obtain ⟨_,hGround,_⟩ := sourcePure_prop_pc_counts_analytic p (by omega) 1
    (by positivity) h univ MeasurableSet.univ (by simp)
  obtain ⟨R,hR,hgood⟩ := hGround (ε/2) (half_pos hε)
  have hprob := hgood R le_rfl
  let G (n : ℕ) := {J : Disorder (n+3) μ.maxDegree |
    actualScoreWindowCount (n+2) c (K n R) (fun _ _ => 1) J ≠ 0 ∧
      sourceSphereMaximum (n+1) μ Q J < sourcePureAnalyticCenter (n+3) E (β*x)+R}
  have hEv : ∀ᶠ n : ℕ in atTop,
      1-ε < (disorderLaw (n+3) μ.maxDegree).real (G n) := by
    apply eventually_lt_of_lt_liminf
      (lt_of_lt_of_le (by linarith : 1-ε < 1-ε/2) hprob)
      (isBoundedUnder_of ⟨0,fun _ => measureReal_nonneg⟩)
  have hcenter (n : ℕ) : sourcePureAnalyticCenter (n+3) E (β*x) =
      s*pureSourceCenter p hp (n+1) := by
    simpa only [sourcePureAnalyticCenter, Nat.add_assoc] using
      (SourcePureCaptureLiteralConsumer.pure_source_consumer_center_eq p hp h (n+1)).symm
  have hEv' : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+3) μ.maxDegree).real
        {J | R/s < |sourceSphereMaximum (n+1) μ 1 J-pureSourceCenter p hp (n+1)|} ≤ ε := by
    filter_upwards [hEv] with n hn
    let B := {J : Disorder (n+3) μ.maxDegree |
      |sourceSphereMaximum (n+1) μ 1 J-pureSourceCenter p hp (n+1)| ≤ R/s}
    have hB : MeasurableSet B := (isClosed_le
      (((sourceSphereMaximum_continuous (n+1) μ 1).sub continuous_const).abs)
      continuous_const).measurableSet
    have hsub : G n ⊆ B := by
      intro J hJ
      have hcount := hJ.1
      have hex : ∃ u : Vector (n+3), ‖u‖^2=(n+3 : ℕ) ∧
          surfaceGradient (field c J) u=0 ∧ actualScore c J u ∈ K n R := by
        by_contra hnex
        have hempty : IsEmpty {u : Vector (n+3) | ‖u‖^2=(n+3 : ℕ) ∧
            surfaceGradient (field c J) u=0 ∧ actualScore c J u ∈ K n R} :=
          ⟨fun u => hnex ⟨u,u.2⟩⟩
        have hempty' : IsEmpty {u : Vector (n+2+1) | ‖u‖^2=(n+2+1 : ℕ) ∧
            surfaceGradient (field c J) u=0 ∧ actualScore c J u ∈ K n R} := hempty
        let _ := hempty'
        exact hcount (by unfold actualScoreWindowCount; exact tsum_empty)
      obtain ⟨u,hu,_,hKu⟩ := hex
      have henergy := (actualScore_mem_physicalEnergyWindow (by omega) c J u _ _).mp hKu
      obtain ⟨v,_,_,hmax,hval⟩ := sourceSphereMaximum_attained (n+1) μ Q J
      have hlo : sourcePureAnalyticCenter (n+3) E (β*x)-R ≤
          sourceSphereMaximum (n+1) μ Q J := henergy.1.1.trans (by rw [hval]; exact hmax hu)
      have hhi := hJ.2.le
      rw [hcenter, pure_sourceSphereMaximum_eq_original_scale p (by omega) 1
        (by positivity) h.overlap_range.1] at hlo hhi
      change |sourceSphereMaximum (n+1) μ 1 J-pureSourceCenter p hp (n+1)| ≤ R/s
      apply abs_le.mpr
      constructor
      · rw [← neg_div]
        apply (div_le_iff₀ hs).mpr
        dsimp only [s] at *
        nlinarith
      · apply (le_div_iff₀ hs).mpr
        dsimp only [s] at *
        nlinarith
    have hmono := measureReal_mono (μ := disorderLaw (n+3) μ.maxDegree)
      hsub (measure_ne_top _ _)
    have hcompl := measureReal_compl hB (μ := disorderLaw (n+3) μ.maxDegree)
    have hevent : {J : Disorder (n+3) μ.maxDegree |
        R/s < |sourceSphereMaximum (n+1) μ 1 J-pureSourceCenter p hp (n+1)|} = Bᶜ := by
      ext J
      simp only [B,mem_ofPred_eq,mem_compl_iff,not_le]
    rw [hevent]
    rw [hcompl]
    simp only [probReal_univ]
    linarith
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hEv'
  refine ⟨R/s,div_pos hR hs,?_⟩
  filter_upwards [eventually_ge_atTop (n₀+1)] with n hn
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
  have hj' : n=j+1 := by omega
  clear hj
  subst n
  have hh := hn₀ j (by omega)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hh

/-- `lem:pc-tight`: uniform tightness about the exact logarithmic center
for every manuscript dimension `N ≥ 2`, including the finite initial segment. -/
theorem pure_original_maximum_tightness
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | L < |sourceSphereMaximum n
          (FiniteMixture.pure p (by omega) 1 (by positivity)) 1 J-
            pureSourceCenter p hp n|} ≤ ε := by
  classical
  intro ε hε
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨L,hL,heventual⟩ := pure_maximum_eventual_tightness p hp h hε
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp heventual
  have hinitial : ∀ n : Fin n₀, ∃ R : ℝ, 0 < R ∧
      (disorderLaw (n.val+2) μ.maxDegree).real
        {J | R < |sourceSphereMaximum n.val μ 1 J-pureSourceCenter p hp n.val|} ≤ ε := by
    intro n
    exact real_random_variable_tail _ _
      ((sourceSphereMaximum_continuous n.val μ 1).measurable.sub measurable_const) hε
  choose R hR htail using hinitial
  let L' := L + ∑ n : Fin n₀, R n
  have hLL : L ≤ L' := le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => (hR n).le)
  refine ⟨L',hL.trans_le hLL,?_⟩
  intro n
  by_cases hn : n₀ ≤ n
  · exact (measureReal_mono (fun _ hJ => hLL.trans_lt hJ) (measure_ne_top _ _)).trans
      (hn₀ n hn)
  · let i : Fin n₀ := ⟨n,by omega⟩
    have hi : R i ≤ L' := by
      have hh := Finset.single_le_sum (fun j _ => (hR j).le) (Finset.mem_univ i)
      dsimp only [L']
      linarith
    exact (measureReal_mono (fun _ hJ => hi.trans_lt hJ) (measure_ne_top _ _)).trans
      (htail i)

/-- The stronger exponential upper tail also closes the second clause of
`lem:pc-tight`, with exponent `c_p` rather than `c_p/2`. -/
theorem pure_original_maximum_exponential_upper_tail
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 ≤ L →
      Filter.limsup (pureSourceMaximumFailure p hp L) atTop ≤
        C * Real.exp (-pureIntensityConstant p (by omega)*L) := by
  obtain ⟨C,hC,hh⟩ := pure_original_source_maximum_upper p hp h
  exact ⟨C,hC,fun L _ => hh L⟩

private theorem sphere_open_neighborhood_positive {N : ℕ} (hN : 1 ≤ N)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ))
    (U : Set (Vector N)) (hU : IsOpen U) (huU : u ∈ U) :
    0 < sphereLaw N U := by
  let : (ProbabilityTheory.gaussianReal 0 1).IsOpenPosMeasure :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
  have hg : (ProbabilityTheory.stdGaussian (Vector N)).IsOpenPosMeasure := by
    rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).isOpenPosMeasure_map
      (WithLp.toLp_surjective 2)
  let _ := hg
  have hne : u ≠ 0 := by
    intro hz
    have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [hz,norm_zero,zero_pow (by norm_num)] at hu
    linarith
  have hn : ‖u‖ = Real.sqrt (N : ℝ) :=
    (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; exact hu)
  have hfix : SphericalAging.SphereInitialLaw.normalize N u = u := by
    unfold SphericalAging.SphereInitialLaw.normalize
    rw [← hn,div_self (norm_ne_zero_iff.mpr hne),one_smul]
  have hc : ContinuousAt (SphericalAging.SphereInitialLaw.normalize N) u := by
    unfold SphericalAging.SphereInitialLaw.normalize
    exact (continuousAt_const.div continuous_norm.continuousAt
      (norm_ne_zero_iff.mpr hne)).smul continuousAt_id
  have hpre : SphericalAging.SphereInitialLaw.normalize N ⁻¹' U ∈ 𝓝 u := by
    apply hc.preimage_mem_nhds
    rw [hfix]
    exact hU.mem_nhds huU
  obtain ⟨V,hVsub,hVopen,huV⟩ := mem_nhds_iff.mp hpre
  change 0 < (ProbabilityTheory.stdGaussian (Vector N)).map
    (SphericalAging.SphereInitialLaw.normalize N) U
  rw [Measure.map_apply (SphericalAging.SphereInitialLaw.normalize_measurable N)
    hU.measurableSet]
  exact (hVopen.measure_pos _ ⟨u,huV⟩).trans_le (measure_mono hVsub)

/-- The literal replicated band has positive product surface volume for
`N ≥ k+1`: choose orthogonal tangent directions at the exact latitude and
take an open neighborhood of the resulting replica tuple. -/
theorem replicatedBand_volume_positive {N k : ℕ} (hNk : k+1 ≤ N) (hk : 1 ≤ k)
    {Q δ ρ : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) (hρ : 0 < ρ)
    (m : Vector N) (hm : ‖m‖^2=(N : ℝ)*Q) :
    0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k Q δ ρ m) := by
  classical
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (show 1 ≤ N by omega)
  have hn' : N=n+1 := by omega
  clear hn
  subst N
  let u := (Real.sqrt Q)⁻¹ • m
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ.1
  have hu : ‖u‖^2=(n+1 : ℕ) := by
    dsimp [u]
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,Real.sq_sqrt hQ.1.le,hm]
    field_simp [hQ.1.ne']
  have hu' : ‖u‖^2=(n+1 : ℕ) := by simpa only [Nat.add_comm] using hu
  let ω (i : Fin k) : Vector (n+1) := IntrinsicHessianLaw.tangentFrame u hu'
    ⟨i.val,by omega⟩
  let t := Real.sqrt ((n+1 : ℕ)*(1-Q))
  let σ (i : Fin k) : Vector (n+1) := m+t • ω i
  have hωnorm (i : Fin k) : ‖ω i‖=1 :=
    (IntrinsicHessianLaw.tangentFrame_orthonormal u hu').norm_eq_one _
  have hωm (i : Fin k) : inner ℝ (ω i) m=0 := by
    have hh := IntrinsicHessianLaw.tangentFrame_tangent u hu' ⟨i.val,by omega⟩
    change inner ℝ (ω i) ((Real.sqrt Q)⁻¹ • m)=0 at hh
    rw [real_inner_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hroot.ne')
  have hmω (i : Fin k) : inner ℝ m (ω i)=0 := by
    rw [real_inner_comm]
    exact hωm i
  have hωpair (i j : Fin k) (hij : i ≠ j) : inner ℝ (ω i) (ω j)=0 := by
    apply (IntrinsicHessianLaw.tangentFrame_orthonormal u hu').inner_eq_zero
    intro heq
    apply hij
    exact Fin.ext (congrArg (fun i : Fin n => i.val) heq)
  have ht : t^2=(n+1 : ℕ)*(1-Q) := Real.sq_sqrt
    (mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hQ.2).le)
  have hσnorm (i : Fin k) : ‖σ i‖^2=(n+1 : ℕ) := by
    dsimp [σ]
    rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hωnorm,one_pow,
      mul_one,hm,real_inner_smul_right,hmω,mul_zero,ht]
    ring
  have hσm (i : Fin k) : overlap (σ i) m=Q := by
    unfold overlap
    dsimp [σ]
    rw [inner_add_left,real_inner_self_eq_norm_sq,hm,real_inner_smul_left,hωm,mul_zero,add_zero]
    exact mul_div_cancel_left₀ Q (by positivity : (n+1 : ℕ) ≠ (0 : ℝ))
  have hσpair (i j : Fin k) (hij : i ≠ j) : overlap (σ i) (σ j)=Q := by
    unfold overlap
    dsimp [σ]
    simp only [inner_add_left,inner_add_right,real_inner_self_eq_norm_sq,hm,
      real_inner_smul_left,real_inner_smul_right,hωm,hmω,hωpair i j hij]
    simp only [mul_zero,add_zero]
    exact mul_div_cancel_left₀ Q (by positivity : (n+1 : ℕ) ≠ (0 : ℝ))
  let O : Set (Fin k → Vector (n+1)) :=
    {z | (∀ i, |overlap (z i) m-Q| < δ*Real.sqrt Q) ∧
      ∀ i j, i ≠ j → |overlap (z i) (z j)-Q| < ρ}
  have hO : IsOpen O := by
    simp only [O,Set.ofPred_and,Set.ofPred_forall]
    apply IsOpen.inter
    · exact isOpen_iInter_of_finite fun i => isOpen_lt (by unfold overlap; fun_prop) continuous_const
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _ => isOpen_lt (by unfold overlap; fun_prop) continuous_const
  have hσO : σ ∈ O := by
    exact ⟨fun i => by rw [hσm,sub_self,abs_zero]; positivity,
      fun i j hij => by rw [hσpair i j hij,sub_self,abs_zero]; exact hρ⟩
  obtain ⟨V,hV,hVsub⟩ := isOpen_pi_iff'.mp hO σ hσO
  have hVpos : ∀ i : Fin k, 0 < sphereLaw (n+1) (V i) := by
    intro i
    exact sphere_open_neighborhood_positive (by omega) (σ i) (hσnorm i)
      (V i) (hV i).1 (hV i).2
  have hsub : univ.pi V ⊆ ReplicatedBand k Q δ ρ m := by
    intro z hz
    have hzO := hVsub hz
    exact ⟨fun i => (hzO.1 i).le,hzO.2⟩
  have hprod : 0 < (Measure.pi (fun _ : Fin k => sphereLaw (n+1))) (univ.pi V) := by
    rw [Measure.pi_pi]
    rw [CanonicallyOrderedAdd.prod_pos]
    exact fun i _ => hVpos i
  exact hprod.trans_le (measure_mono hsub)

private theorem replicated_integrand_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    Integrable (fun σ : Fin k → Vector N =>
      Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (σ i)-field (mixtureCoefficients μ) J m)))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) := by
  have hi := partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β
    ((field_contDiff (mixtureCoefficients μ) J).continuous.sub
      (continuous_const (y := field (mixtureCoefficients μ) J m)))
  have hh := Integrable.fintype_prod (fun _ : Fin k => hi)
  convert hh using 1
  ext σ
  rw [Finset.mul_sum,Real.exp_sum]
  rfl

private theorem replicated_pressure_le_full_pressure {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) (μ : FiniteMixture) (β Q δ ρ : ℝ)
    (J : Disorder N μ.maxDegree) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k Q δ ρ m)) :
    replicatedBandPressure k μ β Q δ ρ J m ≤
      (Real.log (mixturePartition μ β J)-β*field (mixtureCoefficients μ) J m)/(N : ℝ) := by
  have hi := replicated_integrand_integrable (k := k) hN μ β J m
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k Q δ ρ m)) :=
    ⟨hvol.ne'⟩
  have hz : 0 < replicatedBandPartition k μ β Q δ ρ J m := integral_exp_pos hi.restrict
  have hb : replicatedBandPartition k μ β Q δ ρ J m ≤
      Real.exp (-(k : ℝ)*β*field (mixtureCoefficients μ) J m) * mixturePartition μ β J^k := by
    calc
      _ ≤ ∫ σ : Fin k → Vector N,
          Real.exp (β*∑ i : Fin k,
            (field (mixtureCoefficients μ) J (σ i)-field (mixtureCoefficients μ) J m))
          ∂Measure.pi (fun _ : Fin k => sphereLaw N) :=
        setIntegral_le_integral hi (.of_forall fun _ => (Real.exp_pos _).le)
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,mul_sub,Real.exp_sub,Finset.mul_sum,Real.exp_sum]
        rw [integral_div,integral_fintype_prod_eq_pow
          (fun x : Vector N => Real.exp (β*field (mixtureCoefficients μ) J x)),
          Fintype.card_fin,div_eq_mul_inv,← Real.exp_neg]
        change (mixturePartition μ β J)^k * _ = _
        rw [mul_comm]
        congr 1
        congr 1
        ring
  have hZ := mixturePartition_pos hN μ β J
  have hh := Real.log_le_log hz hb
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hZ.ne'),Real.log_exp,Real.log_pow] at hh
  unfold replicatedBandPressure
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  apply (div_le_iff₀ (mul_pos hNr hkr)).mpr
  convert hh using 1
  field_simp
  ring

/-- A coarse dimension- and replica-uniform expected-pressure bound. This
handles every width outside the small-width range of the projection proof. -/
theorem expectedReplicatedBandPressure_coarse_upper {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (Q δ ρ : ℝ) (m : Vector N) :
    expectedReplicatedBandPressure k μ β Q δ ρ m ≤ β^2*μ.xi 1/2 := by
  have hnonneg : 0 ≤ β^2*μ.xi 1/2 := by
    have := μ.xi_pos (by norm_num : (0 : ℝ) < 1)
    positivity
  by_cases hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k Q δ ρ m)
  · by_cases hint : Integrable (replicatedBandPressure k μ β Q δ ρ · m)
        (disorderLaw N μ.maxDegree)
    · have hiZ := mixture_logPartition_integrable hN μ hβ
      have hiH := (field_memLp (mixtureCoefficients μ) m).integrable (by norm_num)
      have hh := integral_mono hint ((hiZ.sub (hiH.const_mul β)).div_const (N : ℝ))
        (fun J => replicated_pressure_le_full_pressure hN hk μ β Q δ ρ J m hvol)
      dsimp only [Pi.sub_apply] at hh
      rw [integral_div,integral_sub hiZ (hiH.const_mul β),integral_const_mul,field_mean,
        mul_zero,sub_zero] at hh
      exact hh.trans (quenchedPressure_le_annealed hN μ hβ)
    · rw [expectedReplicatedBandPressure,integral_undef hint]
      exact hnonneg
  · have hzero : (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k Q δ ρ m)=0 :=
      le_antisymm (not_lt.mp hvol) bot_le
    have hpoint (J : Disorder N μ.maxDegree) : replicatedBandPressure k μ β Q δ ρ J m=0 := by
      simp [replicatedBandPressure,replicatedBandPartition,Measure.restrict_eq_zero.mpr hzero]
    simp only [expectedReplicatedBandPressure,hpoint,integral_zero]
    exact hnonneg

/-- The full width range in `lem:pc-replica-mean`, with no positive-volume
premise. The constant is chosen before width, pair tolerance and replica
count; the dimension threshold is uniform over all centers of that norm. -/
theorem expectedReplicatedBandPressure_full_width_upper
    (μ : FiniteMixture) {β Q : ℝ} (hβ : 0 < β) (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) (Real.sqrt Q/2),
      ∀ ρ : ℝ, 0 < ρ → ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ m : Vector N, ‖m‖^2=(N : ℝ)*Q →
          expectedReplicatedBandPressure k μ β Q δ ρ m ≤
            Real.log (1-Q)/2 + β^2*residualAtOne μ Q/2 + C*Real.sqrt δ +
              C*Real.sqrt (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q)) + ε := by
  obtain ⟨C₀,hC₀,hsmall⟩ := expectedReplicatedBandPressure_upper μ hβ hQ
  let d := (1-Real.sqrt Q)/2
  let T := Real.log (1-Q)/2 + β^2*residualAtOne μ Q/2
  let B := β^2*μ.xi 1/2
  have hd : 0 < d := by
    have hroot : Real.sqrt Q < 1 :=
      (Real.sqrt_lt hQ.1.le (by norm_num)).mpr (by simpa using hQ.2)
    dsimp only [d]
    linarith
  have hB : 0 ≤ B := by
    have := μ.xi_pos (by norm_num : (0 : ℝ) < 1)
    dsimp only [B]
    positivity
  let D := (B+|T|+1)/Real.sqrt d
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDmul : D*Real.sqrt d=B+|T|+1 := div_mul_cancel₀ _ (Real.sqrt_pos.mpr hd).ne'
  refine ⟨C₀+D,add_pos hC₀ hD,?_⟩
  intro δ hδ ρ hρ k hk ε hε
  by_cases hδd : δ ≤ d
  · filter_upwards [hsmall δ hδ.1 hδ.2 hδd ρ hρ k hk ε hε,
      eventually_ge_atTop (k+1)] with N hN hNk
    intro m hm
    have hh := hN m hm (replicatedBand_volume_positive hNk hk hQ hδ.1 hρ m hm)
    have he : C₀*(Real.sqrt δ+
        Real.sqrt (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q))) ≤
        (C₀+D)*Real.sqrt δ +
          (C₀+D)*Real.sqrt (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q)) := by
      nlinarith [mul_nonneg hD.le (Real.sqrt_nonneg δ),
        mul_nonneg hD.le (Real.sqrt_nonneg (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q)))]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro m _
    have hh := expectedReplicatedBandPressure_coarse_upper hN hk μ hβ Q δ ρ m
    have hroot : Real.sqrt d ≤ Real.sqrt δ := Real.sqrt_le_sqrt (not_le.mp hδd).le
    have hlarge : B+|T|+1 ≤ D*Real.sqrt δ := by
      rw [← hDmul]
      exact mul_le_mul_of_nonneg_left hroot hD.le
    have hnonneg₁ := mul_nonneg hC₀.le (Real.sqrt_nonneg δ)
    have hnonneg₂ := mul_nonneg (add_pos hC₀ hD).le
      (Real.sqrt_nonneg (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q)))
    change expectedReplicatedBandPressure k μ β Q δ ρ m ≤
      T+(C₀+D)*Real.sqrt δ+
        (C₀+D)*Real.sqrt (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q))+ε
    dsimp only [B] at hlarge
    nlinarith [neg_le_abs T]

/-- The printed full-width limsup bound. The expected pressures remain
ordinary real Bochner integrals; `EReal` gives limsup its conventional
extended-real meaning, including a possible limit of minus infinity.
An ordinary-real `Filter.limsup` is totalized to zero for an unbounded-below
sequence, so using it without a separate lower-bound proof would not encode
the manuscript limit. The preceding theorem also supplies the equivalent
eventual upper bound with every positive error. -/
theorem expectedReplicatedBandPressure_full_width_limsup
    (μ : FiniteMixture) {β Q : ℝ} (hβ : 0 < β) (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) (Real.sqrt Q/2),
      ∀ ρ : ℝ, 0 < ρ → ∀ k : ℕ, 1 ≤ k →
        ∀ m : (N : ℕ) → Vector N, (∀ N, ‖m N‖^2=(N : ℝ)*Q) →
          Filter.limsup (fun N =>
            (expectedReplicatedBandPressure k μ β Q δ ρ (m N) : EReal)) atTop ≤
            ((Real.log (1-Q)/2 + β^2*residualAtOne μ Q/2 + C*Real.sqrt δ +
              C*Real.sqrt (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q)) : ℝ) : EReal) := by
  obtain ⟨C,hC,hh⟩ := expectedReplicatedBandPressure_full_width_upper μ hβ hQ
  refine ⟨C,hC,?_⟩
  intro δ hδ ρ hρ k hk m hm
  let B := Real.log (1-Q)/2 + β^2*residualAtOne μ Q/2 + C*Real.sqrt δ +
    C*Real.sqrt (1/(k : ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q))
  have hb (j : ℕ) : Filter.limsup (fun N =>
      (expectedReplicatedBandPressure k μ β Q δ ρ (m N) : EReal)) atTop ≤
        ((B+1/((j : ℝ)+1) : ℝ) : EReal) := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [hh δ hδ ρ hρ k hk (1/((j : ℝ)+1)) (by positivity)] with N hN
    exact EReal.coe_le_coe (hN (m N) (hm N))
  have hlim : Tendsto (fun j : ℕ => ((B+1/((j : ℝ)+1) : ℝ) : EReal))
      atTop (𝓝 (B : EReal)) := by
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    simpa only [add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add B
  exact ge_of_tendsto hlim (.of_forall hb)

end SlowEquilibration.SourcePureSection9SmallClosures
