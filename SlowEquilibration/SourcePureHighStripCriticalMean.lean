-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureGlobalMaximumCoarseTail
public import SlowEquilibration.SourcePureLocalMaxTailUpper

/-! The actual all-critical first moment in a fixed high-energy compact
strip vanishes exponentially fast above the proper-pure contact. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open SlowEquilibration.PairConditionalDeterminantMoments ExpectedTailCentering
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem sourcePure_high_strip_mean_eq_truncated
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q l r s t : ℝ) (hls : l < s) (htr : t < r) :
    sourceUnfilteredValueWindowMean (n+1) (FiniteMixture.pure p hp a ha) Q
      (Icc s t) =
    sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r
      ((n+2 : ℕ)*s) ((n+2 : ℕ)*t) := by
  change sourceUnfilteredValueWindowMean (n+1) (FiniteMixture.pure p hp a ha) Q
    (Icc s t) = sourceUnfilteredValueWindowMean (n+1)
      (FiniteMixture.pure p hp a ha) Q
      ((fun b : ℝ => (n+2 : ℕ)*b) ⁻¹'
        (Icc ((n+2 : ℕ)*s) ((n+2 : ℕ)*t) ∩
          Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)))
  congr 1
  ext b
  have hN : (0 : ℝ) < (n+2 : ℕ) := by positivity
  simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ioo]
  constructor
  · intro hb
    refine ⟨⟨mul_le_mul_of_nonneg_left hb.1 hN.le,
      mul_le_mul_of_nonneg_left hb.2 hN.le⟩,?_,?_⟩
    · exact (mul_lt_mul_of_pos_left (hls.trans_le hb.1) hN)
    · exact (mul_lt_mul_of_pos_left (hb.2.trans_lt htr) hN)
  · intro hb
    exact ⟨(mul_le_mul_iff_right₀ hN).mp hb.1.1,
      (mul_le_mul_iff_right₀ hN).mp hb.1.2⟩

theorem sourcePure_high_strip_critical_mean_tendsto_zero
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {s t : ℝ} (hs : markE (FiniteMixture.pure p hp a ha) β x Q < s)
    (hst : s ≤ t) :
    Tendsto (fun n : ℕ => sourceUnfilteredValueWindowMean (n+1)
      (FiniteMixture.pure p hp a ha) Q (Icc s t)) atTop (𝓝 (0 : ℝ)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let δMax := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(4*(p : ℝ))
  let δ := δMax/2
  let l := E-δ
  let r := t+1
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hδMax : 0 < δMax := div_pos hedge (by positivity)
  have hδ : 0 < δ := half_pos hδMax
  have hδBound : δ ≤ δMax := by dsimp [δ]; linarith
  have hEl : E ∈ Ioo l r := by
    constructor <;> dsimp [l,r] <;> linarith
  have hls : l < s := by dsimp [l]; linarith
  have htr : t < r := by dsimp [r]; linarith
  have hg : 0 < (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2 :=
    div_pos hedge (by norm_num)
  have hLeft : 2*Real.sqrt (Q^2*μ.xi2 Q)+
      (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2 ≤ (p : ℝ)*l :=
    source_pure_value_box_edge_margin p hp a ha h hδBound l
      (by dsimp [l];constructor <;> linarith)
  obtain ⟨C,c,hC,hc,hCompare⟩ := sourcePure_criticalWindowMean_relative_comparison
    p hp a ha h hEl hg hLeft (le_refl ((p : ℝ)*r))
  obtain ⟨A,hA,hTail⟩ := sourcePure_truncatedLocalMax_tail_global_upper
    p hp a ha h (hEl.1.trans hEl.2) hg hLeft (le_refl ((p : ℝ)*r))
  have hInt := pureTruncatedLocalMaxDensity_integrable_eventually
    p hp a ha h (hEl.1.trans hEl.2) hg hLeft (le_refl ((p : ℝ)*r))
  let z : ℕ → ℝ := fun n =>
    A/(β*x)*Real.exp (-(β*x)*((n+2 : ℕ)*(s-E))) / Real.sqrt (n+2 : ℕ)
  have hbound : ∀ᶠ n : ℕ in atTop,
      sourceUnfilteredValueWindowMean (n+1) μ Q (Icc s t) ≤
        (1+C*Real.exp (-c*(n+2 : ℕ)))*z n := by
    filter_upwards [hCompare,hTail,hInt] with n hn ht hi
    rw [sourcePure_high_strip_mean_eq_truncated n p hp a ha Q l r s t hls htr]
    have hw := (hn ((n+2 : ℕ)*s) ((n+2 : ℕ)*t)).2
    have hlocal : sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r
        ((n+2 : ℕ)*s) ((n+2 : ℕ)*t) ≤
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) ((n+2 : ℕ)*s) := by
      rw [sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha
        h.overlap_range.1]
      apply setIntegral_mono_set hi.integrableOn
        (ae_of_all _ (fun H => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ H))
      exact ae_of_all _ (fun H hH => hH.1)
    have hz := ht ((n+2 : ℕ)*s)
    have hfac : 0 ≤ 1+C*Real.exp (-c*(n+2 : ℕ)) := by positivity
    calc
      _ ≤ (1+C*Real.exp (-c*(n+2 : ℕ)))*
          sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r
            ((n+2 : ℕ)*s) ((n+2 : ℕ)*t) := hw
      _ ≤ (1+C*Real.exp (-c*(n+2 : ℕ)))*
          tail (pureTruncatedLocalMaxDensity n p hp a ha Q
            ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) ((n+2 : ℕ)*s) :=
        mul_le_mul_of_nonneg_left hlocal hfac
      _ ≤ (1+C*Real.exp (-c*(n+2 : ℕ)))*z n := by
        apply mul_le_mul_of_nonneg_left _ hfac
        have hshift : (n+2 : ℕ)*s-(n+2 : ℕ)*E =
            (n+2 : ℕ)*(s-E) := by ring
        rw [hshift] at hz
        simpa only [z,E] using hz
  have hzero : Tendsto z atTop (𝓝 (0 : ℝ)) := by
    have hdim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    have hrate : 0 < (β*x)*(s-E) :=
      mul_pos (mul_pos h.beta_pos h.weight_range.1) (by dsimp [E]; linarith)
    have hexp : Tendsto (fun n : ℕ =>
        Real.exp (-(β*x)*(n+2 : ℕ)*(s-E))) atTop (𝓝 (0 : ℝ)) := by
      have ht := Real.tendsto_exp_atBot.comp
        (hdim.const_mul_atTop_of_neg (neg_neg_of_pos hrate))
      convert ht using 1
      · funext n
        congr 1
        ring
    have hnum : Tendsto (fun n : ℕ =>
        A/(β*x)*Real.exp (-(β*x)*(n+2 : ℕ)*(s-E))) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hexp.const_mul (A/(β*x))
    have hroot := NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero
    have hmul := hnum.mul hroot
    convert hmul using 1
    · funext n
      dsimp [z]
      ring
    · ring
  have hfactor : Tendsto (fun n : ℕ => 1+C*Real.exp (-c*(n+2 : ℕ))) atTop
      (𝓝 (1 : ℝ)) := by
    have hdim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    have hexp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ)))
        atTop (𝓝 (0 : ℝ)) :=
      Real.tendsto_exp_atBot.comp
        (hdim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.add (hexp.const_mul C) :
        Tendsto (fun n : ℕ => 1+C*Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (1+C*0)))
  have hlow : ∀ n : ℕ, 0 ≤ sourceUnfilteredValueWindowMean (n+1) μ Q (Icc s t) :=
    fun _ => ENNReal.toReal_nonneg
  exact squeeze_zero' (Filter.Eventually.of_forall hlow) hbound
    (by simpa only [mul_zero] using hfactor.mul hzero)

end SlowEquilibration.SphericalMarkedWindows
