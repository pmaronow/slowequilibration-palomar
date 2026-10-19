-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureLiteralConsumer
public import SlowEquilibration.SourcePurePCCountsLiteral

/-! Manuscript `prop:pc-separation` and `cor:pc-disjoint` for the actual
original pure field. Separation is the explicitly supplied published result
Subag, *The geometry of the Gibbs measure of pure spherical spin glasses*,
Inventiones mathematicae 210 (2017), Corollary 13, equation (2.11),
https://arxiv.org/abs/1604.00679. Applying that result to `-H_N` gives the
maximum convention here; shrinking the open energy interval gives the closed
endpoints. `Corollary13` is a proposition interface, never an axiom.
The cap geometry, antipodal case, window inclusion, and probability assembly
are proved below, rather than included in the literature interface. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureSeparationDisjoint
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalForm SphereHessian SphericalTAPCertificate PureStationarity
open SphericalPureCapSourceScalars SphericalPureCapCenteringIdentity
open SourcePureCaptureFixedCapEstimates SourcePureCaptureBandComplementBound
open SourcePureCaptureWindowTransport SourcePureCaptureLiteralConsumer
open SphericalPureCenterFieldScale
open PairConditionalDeterminantMoments TwoAtomStationarity
open scoped Topology ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Actual critical points in the closed near-ground energy interval. -/
def nearGroundCriticalSet (p : ℕ) (hp : 3 ≤ p) (n : ℕ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
    (d : ℝ) : Set (Vector (n+2)) :=
  originalEnergyCriticalSet n (FiniteMixture.pure p (by omega) 1 (by positivity))
    (Icc ((n+2:ℕ)*(pureEnergyConstant p hp-d))
      ((n+2:ℕ)*(pureEnergyConstant p hp+d))) J

/-- The additional published separation input, in the exact one-sided,
closed-endpoint version used by the manuscript. It imposes no temperature
assumption and includes every `p≥3`. No conclusion about bands is assumed. -/
def Corollary13 (p : ℕ) (hp : 3 ≤ p) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
      {J | ∃ u ∈ nearGroundCriticalSet p hp n J d,
        ∃ v ∈ nearGroundCriticalSet p hp n J d,
          u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} ≤ Real.exp (-c*(n+2:ℕ))

/-- Literal source `prop:pc-separation`, conditional only on the additional
published Corollary 13 interface. -/
theorem pure_original_critical_separation (p : ℕ) (hp : 3 ≤ p)
    (hSubag : Corollary13 p hp) (ε : ℝ) (hε : 0 < ε) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | ∃ u ∈ nearGroundCriticalSet p hp n J d,
          ∃ v ∈ nearGroundCriticalSet p hp n J d,
            u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} ≤ Real.exp (-c*(n+2:ℕ)) :=
  hSubag ε hε

/-- The original-energy critical window `D_{N,L}`, counting both antipodes. -/
def criticalWindow (p : ℕ) (hp : 4 ≤ p) (n : ℕ) (L : ℝ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
    Set (Vector (n+2)) :=
  originalEnergyCriticalSet n (FiniteMixture.pure p (by omega) 1 (by positivity))
    (Icc (pureSourceCenter p hp n-L) (pureSourceCenter p hp n+L)) J

/-- The number of points of `D_{N,L}`, with no quotient by antipodes. -/
def criticalWindowCount (p : ℕ) (hp : 4 ≤ p) (n : ℕ) (L : ℝ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) : ℝ≥0∞ :=
  ∑' _u : criticalWindow p hp n L J, (1:ℝ≥0∞)

private theorem criticalWindowCount_eq_center_count (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (n : ℕ) (L : ℝ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    criticalWindowCount p hp n L J =
      actualScoreWindowCount (n+1) (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+2)
          (Icc (sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x)-(Real.sqrt Q)^p*L)
            (sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x)+(Real.sqrt Q)^p*L)) univ)
        (fun _ _ => 1) J := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p
  have hcenter : sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x) =
      s*pureSourceCenter p hp n := (pure_source_consumer_center_eq p hp h n).symm
  rw [hcenter,actual_pure_scoreWindowCount_eq_valueWindowCount]
  have hW : pureScoreWindow p (physicalEnergyWindow (n+2)
      (Icc (s*pureSourceCenter p hp n-s*L) (s*pureSourceCenter p hp n+s*L)) univ) =
      (fun e : ℝ => (n+2:ℕ)*e) ⁻¹'
        Icc (s*pureSourceCenter p hp n-s*L) (s*pureSourceCenter p hp n+s*L) := by
    ext e
    simp [pureScoreWindow,physicalEnergyWindow,rectangularScoreWindow,pureScoreLine]
  rw [hW]
  have hset : {u : Vector (n+2) | ‖u‖^2=(n+2:ℕ) ∧
      surfaceGradient (field c J) u=0 ∧
      (n+2:ℕ)*actualValue c J u ∈
        Icc (s*pureSourceCenter p hp n-s*L) (s*pureSourceCenter p hp n+s*L)} =
      criticalWindow p hp n L J := by
    ext u
    have hgrad := pure_center_surfaceGradient_eq_original_scale p (by omega) 1
      (by positivity) h.overlap_range.1.le (n+2) J u
    have hval : (n+2:ℕ)*actualValue c J u = s*field (mixtureCoefficients μ) J u := by
      unfold actualValue
      rw [pure_center_field_eq_original_scale p (by omega) 1 (by positivity)
        h.overlap_range.1.le]
      field_simp
      rfl
    have hg : surfaceGradient (field c J) u=0 ↔
        surfaceGradient (field (mixtureCoefficients μ) J) u=0 := by
      rw [hgrad]
      change s • surfaceGradient (field (mixtureCoefficients μ) J) u=0 ↔ _
      simp only [smul_eq_zero,hs.ne',false_or]
    simp only [mem_ofPred_eq,criticalWindow,originalEnergyCriticalSet,hg,hval,mem_Icc]
    constructor
    · rintro ⟨hu,hg',hl,hr⟩
      refine ⟨hu,hg',?_,?_⟩
      · exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith only [hl])
      · exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith only [hr])
    · rintro ⟨hu,hg',hl,hr⟩
      have hl' := mul_le_mul_of_nonneg_left hl hs.le
      have hr' := mul_le_mul_of_nonneg_left hr hs.le
      exact ⟨hu,hg',by nlinarith only [hl'],by nlinarith only [hr']⟩
  unfold criticalWindowCount actualValueWindowCount
  change (∑' _u : criticalWindow p hp n L J, (1:ℝ≥0∞)) =
    ∑' _u : {u : Vector (n+2) | ‖u‖^2=(n+2:ℕ) ∧
      surfaceGradient (field c J) u=0 ∧
      (n+2:ℕ)*actualValue c J u ∈
        Icc (s*pureSourceCenter p hp n-s*L) (s*pureSourceCenter p hp n+s*L)}, (1:ℝ≥0∞)
  rw [hset]

/-- Literal all-dimension bounded expected number of original-window
critical points. This part requires no separation literature input. -/
theorem pure_original_criticalWindow_count_bounded (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, ∀ n : ℕ,
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) < ⊤ ∧
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).toReal ≤ C := by
  have hs : 0 < (Real.sqrt Q)^p := pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p
  obtain ⟨C,hC⟩ := (sourcePure_prop_pc_counts_literal p (by omega) 1 (by positivity)
    h univ MeasurableSet.univ (by simp)).1 ((Real.sqrt Q)^p*L) (mul_pos hs hL)
  refine ⟨C,?_⟩
  intro n
  simp_rw [criticalWindowCount_eq_center_count p hp h]
  exact hC n

/-- Literal microscopic band, restricted to the physical sphere. -/
def microscopicBand (n : ℕ) (Q w : ℝ) (u : Vector (n+2)) : Set (Vector (n+2)) :=
  {z | ‖z‖^2=(n+2:ℕ) ∧ |overlap z u-Real.sqrt Q| ≤ w/Real.sqrt (n+2:ℕ)}

/-- Two caps with a common sphere point force the sharp overlap threshold
`2a²-1`, without any trigonometric or large-dimension qualification. -/
theorem common_caps_overlap {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 0 ≤ a)
    (u v z : Vector N) (hu : ‖u‖^2=(N:ℝ)) (hv : ‖v‖^2=(N:ℝ))
    (hz : ‖z‖^2=(N:ℝ)) (hzu : a ≤ overlap z u) (hzv : a ≤ overlap z v) :
    2*a^2-1 ≤ overlap u v := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hzu' := (le_div_iff₀ hNr).mp hzu
  have hzv' := (le_div_iff₀ hNr).mp hzv
  have hproj : 2*a*(N:ℝ) ≤ inner ℝ z (u+v) := by
    rw [inner_add_right]
    change a*(N:ℝ) ≤ inner ℝ z u at hzu'
    change a*(N:ℝ) ≤ inner ℝ z v at hzv'
    linarith
  have hcs := abs_real_inner_le_norm z (u+v)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
  rw [sq_abs,mul_pow,hz,norm_add_sq_real,hu,hv] at hsq
  have hproj2 := (sq_le_sq₀ (by positivity : 0 ≤ 2*a*(N:ℝ))
    ((by positivity : 0 ≤ 2*a*(N:ℝ)).trans hproj)).mpr hproj
  have hh : (N:ℝ)*(2*a^2-1) ≤ inner ℝ u v := by
    have hh' : (N:ℝ)*((N:ℝ)*(2*a^2-1)) ≤ (N:ℝ)*inner ℝ u v := by
      nlinarith only [hsq,hproj2]
    exact (mul_le_mul_iff_right₀ hNr).mp hh'
  exact (le_div_iff₀ hNr).mpr (by nlinarith only [hh])

/-- Opposite centers have disjoint positive caps in every dimension. -/
theorem positive_caps_antipodal {N : ℕ} {a : ℝ} (ha : 0 < a)
    (u z : Vector N) (hzu : a ≤ overlap z u) (hzneg : a ≤ overlap z (-u)) : False := by
  have hn : overlap z (-u) = -overlap z u := by
    unfold overlap
    rw [inner_neg_right,neg_div]
  rw [hn] at hzneg
  linarith

/-- A fixed original-energy logarithmic window is eventually inside every
positive fixed near-ground interval. -/
theorem criticalWindow_eventually_subset_nearGround (p : ℕ) (hp : 4 ≤ p)
    (L : ℝ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ J,
      criticalWindow p hp n L J ⊆ nearGroundCriticalSet p (by omega) n J d := by
  have hbox := source_logarithmic_center_offset_bounds
    (E := pureEnergyConstant p (by omega))
    (pureIntensityConstant_pos p (by omega)) (le_refl (0:ℝ)) hd
    (pureSourceCenter p hp) (by filter_upwards [] with n; simp [pureSourceCenter]) (-L) L
  filter_upwards [hbox] with n hn
  intro J u hu
  exact ⟨hu.1,hu.2.1,hn.1.trans hu.2.2.1,hu.2.2.2.trans hn.2⟩

/-- Fixed microscopic bands eventually lie in any cap below `√Q`. -/
theorem microscopicBand_eventually_subset_cap {Q a : ℝ} (ha : a < Real.sqrt Q)
    (w : ℝ) : ∀ᶠ n : ℕ in atTop, ∀ u z : Vector (n+2),
      z ∈ microscopicBand n Q w u → a ≤ overlap z u := by
  have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hw := (Real.tendsto_sqrt_atTop.comp hN).const_div_atTop w
  have hsmall := hw.eventually (Iio_mem_nhds (sub_pos.mpr ha))
  filter_upwards [hsmall] with n hn
  simp only [Function.comp_def] at hn
  intro u z hz
  have hh := (abs_le.mp hz.2).1
  linarith

/-- Probability-one asymptotic disjointness of the literal microscopic
bands, conditional on separation. No mark or determinant hypothesis enters. -/
theorem pure_original_microscopic_disjointness (p : ℕ) (hp : 4 ≤ p)
    (hSubag : Corollary13 p (by omega)) {Q : ℝ}
    (hQ : 1/2 < Q) (_hQ1 : Q < 1) (L w : ℝ) :
    Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 (1:ℝ)) := by
  classical
  let a := (Real.sqrt (1/2:ℝ)+Real.sqrt Q)/2
  have hroot : Real.sqrt (1/2:ℝ) < Real.sqrt Q := Real.sqrt_lt_sqrt (by norm_num) hQ
  have ha : 0 < a := by dsimp [a]; positivity
  have haq : a < Real.sqrt Q := by dsimp [a]; linarith
  have ha2 : 1/2 < a^2 := by
    have hh : Real.sqrt (1/2:ℝ) < a := by dsimp [a]; linarith
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2), Real.sqrt_nonneg (1/2:ℝ)]
  let ε := 2*a^2-1
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨d,c,hd,hc,hsep⟩ := hSubag ε hε
  have hcap := microscopicBand_eventually_subset_cap haq w
  have hwindow := criticalWindow_eventually_subset_nearGround p hp L hd
  have hbad : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | ¬ (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)} ≤
        Real.exp (-c*(n+2:ℕ)) := by
    filter_upwards [hsep,hcap,hwindow] with n hn hcN hwN
    apply (measureReal_mono _).trans hn
    intro J hJ
    classical
    have hex : ∃ u ∈ criticalWindow p hp n L J,
        ∃ v ∈ criticalWindow p hp n L J, u ≠ v ∧
          ¬ Disjoint (microscopicBand n Q w u) (microscopicBand n Q w v) := by
      simpa only [mem_ofPred_eq,Set.PairwiseDisjoint,Set.Pairwise,
        Function.onFun,not_forall,not_imp,exists_prop] using hJ
    obtain ⟨u,hu,v,hv,huv,hint⟩ := hex
    obtain ⟨z,hzu,hzv⟩ := Set.not_disjoint_iff.mp hint
    have hcu := hcN u z hzu
    have hcv := hcN v z hzv
    have huvneg : u ≠ -v := by
      intro heq
      rw [heq] at hcu
      exact positive_caps_antipodal ha v z hcv hcu
    exact ⟨u,hwN J hu,v,hwN J hv,huv,huvneg,
      common_caps_overlap (by omega) ha.le u v z hu.1 hv.1 hzu.1 hcu hcv⟩
  have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2:ℕ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop hc)
  have hlim : Tendsto (fun n : ℕ => 1-
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ =>
      sub_nonneg.mpr measureReal_le_one) ?_ hExp
    filter_upwards [hbad] with n hn
    have ht := measureReal_union_le
      (μ := disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
      {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)}
      {J | ¬ (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)}
    have heq : {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)} ∪
        {J | ¬ (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)} = univ := by
      ext J
      simp only [mem_union,mem_ofPred_eq,mem_univ]
      exact iff_true_intro (Classical.em _)
    rw [heq,probReal_univ] at ht
    linarith
  simpa using hlim.const_sub 1

/-- Both literal conclusions of `cor:pc-disjoint`: disjoint microscopic
bands with probability tending to one and bounded expected number in every
dimension. Corollary 13 is the only published input; the count bound and
the overlap margin are consequences of the supplied pure certificate. -/
theorem pure_original_disjoint_bands_and_bounded_count (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hSubag : Corollary13 p (by omega)) {L w : ℝ} (hL : 0 < L) (_hw : 0 < w) :
    Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 (1:ℝ)) ∧
    ∃ C : ℝ, ∀ n : ℕ,
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) < ⊤ ∧
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).toReal ≤ C := by
  obtain ⟨a,ha,haq,_⟩ := SphericalPureCapResidualMargin.sourcePure_cap_latitude_choice p hp h
  have hroot : 1/Real.sqrt 2 < Real.sqrt Q := ha.trans haq
  have hsq : (1/Real.sqrt 2)^2=(1/2:ℝ) := by
    rw [div_pow,one_pow,Real.sq_sqrt (by norm_num)]
  have hQhalf : (1/2:ℝ) < Q := by
    have hp0 : 0 < 1/Real.sqrt (2:ℝ) := by positivity
    have hsq' := (sq_lt_sq₀ hp0.le (Real.sqrt_nonneg Q)).mpr hroot
    rw [hsq,Real.sq_sqrt h.overlap_range.1.le] at hsq'
    exact hsq'
  exact ⟨pure_original_microscopic_disjointness p hp hSubag hQhalf h.overlap_range.2 L w,
    pure_original_criticalWindow_count_bounded p hp h hL⟩

end SlowEquilibration.SourcePureSeparationDisjoint
