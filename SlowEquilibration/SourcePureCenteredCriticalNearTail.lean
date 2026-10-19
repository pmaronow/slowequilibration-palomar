-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureMaximumWindowCountBridge
public import SlowEquilibration.SourcePhysicalPairRetainedWindowGeometry
public import SlowEquilibration.ExpectedLogarithmicCentering

/-! A source-derived exponential bound for the all-critical near-contact
window at any correctly logarithmically centered proper-pure sequence. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open SlowEquilibration.PairConditionalDeterminantMoments ExpectedTailCentering
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem sourcePure_centered_near_critical_mean_upper
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let δ := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(8*(p : ℝ))
    let s := E+δ/2
    0 < δ ∧ ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, ∀ᶠ n : ℕ in atTop,
      sourceUnfilteredValueWindowMean (n+1) μ Q
        (Icc ((m n+L)/(n+2 : ℕ)) s) ≤ A*Real.exp (-(β*x)*L) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let δMax := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(4*(p : ℝ))
  let δ := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(8*(p : ℝ))
  let l := E-δ
  let r := E+δ
  let s := E+δ/2
  let b := β*x
  have hb : 0 < b := mul_pos h.beta_pos h.weight_range.1
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hδMax : 0 < δMax := div_pos hedge (by positivity)
  have hδ : 0 < δ := div_pos hedge (by positivity)
  have hδBound : δ ≤ δMax := by
    dsimp [δ,δMax]
    have hpR : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8*(p : ℝ))
      (by positivity : (0 : ℝ) < 4*(p : ℝ))).mpr
    nlinarith [hedge,hpR]
  have hm : E ∈ Ioo l r := by constructor <;> dsimp [l,r] <;> linarith
  have hsr : s < r := by dsimp [s,r]; linarith
  have hg : 0 < (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2 :=
    div_pos hedge (by norm_num)
  have hLeft : 2*Real.sqrt (Q^2*μ.xi2 Q)+
      (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2 ≤ (p : ℝ)*l :=
    source_pure_value_box_edge_margin p hp a ha h hδBound l
      (by dsimp [l];constructor <;> linarith)
  obtain ⟨C,c,hC,hc,hCompare⟩ := sourcePure_criticalWindowMean_relative_comparison
    p hp a ha h hm hg hLeft (le_refl ((p : ℝ)*r))
  obtain ⟨T,hT,hTail⟩ := sourcePure_truncatedLocalMax_tail_global_upper
    p hp a ha h (hm.1.trans hm.2) hg hLeft (le_refl ((p : ℝ)*r))
  have hInt := pureTruncatedLocalMaxDensity_integrable_eventually
    p hp a ha h (hm.1.trans hm.2) hg hLeft (le_refl ((p : ℝ)*r))
  have hdim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (hdim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hfactor : Tendsto (fun n : ℕ => 1+C*Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.add (hexp.const_mul C) :
        Tendsto (fun n : ℕ => 1+C*Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (1+C*0)))
  let A := 2*(T/b)*Real.exp (b*M)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨hδ, A,hA,?_⟩
  intro L
  have hOffset := source_logarithmic_center_offset_bounds hb hM.le
    (half_pos hδ) m hcenter L L
  filter_upwards [hOffset,hCompare,hTail,hInt,hcenter,
    hfactor.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))]
    with n hnOff hnComp hnTail hnInt hnCenter hnFactor
  have hN : (0 : ℝ) < (n+2 : ℕ) := by positivity
  have hls : l < (m n+L)/(n+2 : ℕ) := by
    have hLess : (n+2 : ℕ)*l < m n+L := by
      have hh := hnOff.1
      dsimp [l,E,s] at *
      nlinarith
    exact (lt_div_iff₀ hN).mpr (by simpa only [mul_comm] using hLess)
  have heq := sourcePure_high_strip_mean_eq_truncated n p hp a ha Q l r
    ((m n+L)/(n+2 : ℕ)) s hls hsr
  have hphys : (n+2 : ℕ)*((m n+L)/(n+2 : ℕ))=m n+L :=
    by field_simp
  rw [heq,hphys]
  let f := pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hlocal : sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r
      (m n+L) ((n+2 : ℕ)*s) ≤ tail f (m n+L) := by
    rw [sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha
      h.overlap_range.1]
    apply setIntegral_mono_set hnInt.integrableOn
      (ae_of_all _ (fun H => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ H))
    exact ae_of_all _ (fun H hH => hH.1)
  have htail := hnTail (m n+L)
  let u := m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*b))
  have hu : -M ≤ u := (abs_le.mp hnCenter).1
  have hshift : (m n+L)-(n+2 : ℕ)*E =
      -Real.log (n+2 : ℕ)/(2*b)+(u+L) := by dsimp [u]; ring
  rw [hshift] at htail
  have hscale := reference_scale hN hb (u+L)
  have htail' : tail f (m n+L) ≤ (T/b)*Real.exp (-b*(u+L)) := by
    calc
      _ ≤ (T/b)*(Real.exp (-b*(-Real.log (n+2 : ℕ)/(2*b)+(u+L))) /
          Real.sqrt (n+2 : ℕ)) := by convert htail using 1; ring
      _ = _ := by rw [hscale]
  have hexpUpper : Real.exp (-b*(u+L)) ≤ Real.exp (b*M-b*L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hu hb.le]
  have htailUpper : tail f (m n+L) ≤ (T/b)*Real.exp (b*M-b*L) :=
    htail'.trans (mul_le_mul_of_nonneg_left hexpUpper (by positivity))
  have hfac : 0 ≤ 1+C*Real.exp (-c*(n+2 : ℕ)) := by positivity
  calc
    sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r
        (m n+L) ((n+2 : ℕ)*s) ≤
      (1+C*Real.exp (-c*(n+2 : ℕ)))*
        sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r
          (m n+L) ((n+2 : ℕ)*s) := (hnComp _ _).2
    _ ≤ (1+C*Real.exp (-c*(n+2 : ℕ)))*tail f (m n+L) :=
      mul_le_mul_of_nonneg_left hlocal hfac
    _ ≤ 2*((T/b)*Real.exp (b*M-b*L)) := by
      have htailNonneg : 0 ≤ tail f (m n+L) :=
        integral_nonneg_of_ae (ae_of_all _
          (fun H => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ H))
      have hf := mul_le_mul_of_nonneg_right hnFactor.le htailNonneg
      exact hf.trans (mul_le_mul_of_nonneg_left htailUpper (by norm_num))
    _ = A*Real.exp (-b*L) := by
      dsimp [A]
      rw [show b*M-b*L = b*M+(-b*L) by ring,Real.exp_add]
      ring

end SlowEquilibration.SphericalMarkedWindows
