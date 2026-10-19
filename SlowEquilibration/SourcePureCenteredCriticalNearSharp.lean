-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCenteredCriticalNearTail
public import SlowEquilibration.SourcePureLocalMaxNormalizedLimits
public import Mathlib.Topology.Order.LiminfLimsup

/-! Exact unit-coefficient upper limit for the near-contact original-field
all-critical mean at the very same tail-equals-one center. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open SlowEquilibration.PairConditionalDeterminantMoments ExpectedTailCentering
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem sourcePure_centered_near_critical_mean_sharp
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q δ g : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let s := E+δ/2
    ∀ L η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      sourceUnfilteredValueWindowMean (n+1) μ Q
        (Icc ((m n+L)/(n+2 : ℕ)) s) ≤ Real.exp (-(β*x)*L)+η := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let l := E-δ
  let r := E+δ
  let s := E+δ/2
  let b := β*x
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hb : 0 < b := mul_pos h.beta_pos h.weight_range.1
  have hm : E ∈ Ioo l r := by constructor <;> dsimp [l,r] <;> linarith
  have hsr : s < r := by dsimp [s,r]; linarith
  obtain ⟨C,c,hC,hc,hCompare⟩ := sourcePure_criticalWindowMean_relative_comparison
    p hp a ha h hm hg hLeft (le_refl ((p : ℝ)*r))
  have hInt := pureTruncatedLocalMaxDensity_integrable_eventually
    p hp a ha h (hm.1.trans hm.2) hg hLeft (le_refl ((p : ℝ)*r))
  have hTail : ∀ L : ℝ, Tendsto (fun n : ℕ => tail (f n) (m n+L))
      atTop (𝓝 (Real.exp (-b*L))) := by
    intro L
    simpa only [f,l,r,E,μ,b] using
      (sourcePure_truncatedLocalMax_normalized_limits_of_center
        p hp a ha h hm hg hLeft (le_refl ((p : ℝ)*r)) m hM hcenter).2 L
  have hdim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (hdim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hfactor : Tendsto (fun n => 1+C*Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.add (hexp.const_mul C) :
        Tendsto (fun n : ℕ => 1+C*Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (1+C*0)))
  intro L η hη
  have hcenterBound : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*b))| ≤ M := by
    filter_upwards [hcenter] with n hn
    exact hn.2
  have hOffset := source_logarithmic_center_offset_bounds hb hM.le
    (half_pos hδ) m hcenterBound L L
  have hupper : Tendsto (fun n =>
      (1+C*Real.exp (-c*(n+2 : ℕ)))*tail (f n) (m n+L))
      atTop (𝓝 (Real.exp (-b*L))) := by
    simpa only [one_mul] using hfactor.mul (hTail L)
  have hbound : ∀ᶠ n : ℕ in atTop,
      sourceUnfilteredValueWindowMean (n+1) μ Q
        (Icc ((m n+L)/(n+2 : ℕ)) s) ≤
      (1+C*Real.exp (-c*(n+2 : ℕ)))*tail (f n) (m n+L) := by
    filter_upwards [hOffset,hCompare,hInt] with n hnOff hnComp hnInt
    have hN : (0 : ℝ) < (n+2 : ℕ) := by positivity
    have hls : l < (m n+L)/(n+2 : ℕ) := by
      have hLess : (n+2 : ℕ)*l < m n+L := by
        have hh := hnOff.1
        dsimp [l,E,s] at *
        nlinarith
      exact (lt_div_iff₀ hN).mpr (by simpa only [mul_comm] using hLess)
    have heq := sourcePure_high_strip_mean_eq_truncated n p hp a ha Q l r
      ((m n+L)/(n+2 : ℕ)) s hls hsr
    have hphys : (n+2 : ℕ)*((m n+L)/(n+2 : ℕ))=m n+L := by field_simp
    rw [heq,hphys]
    have hlocal : sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r
        (m n+L) ((n+2 : ℕ)*s) ≤ tail (f n) (m n+L) := by
      rw [sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha
        h.overlap_range.1]
      apply setIntegral_mono_set hnInt.integrableOn
        (ae_of_all _ (fun H => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ H))
      exact ae_of_all _ (fun H hH => hH.1)
    have hfac : 0 ≤ 1+C*Real.exp (-c*(n+2 : ℕ)) := by positivity
    exact (hnComp _ _).2.trans (mul_le_mul_of_nonneg_left hlocal hfac)
  filter_upwards [hbound,
    hupper.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hη))]
    with n hn hlim
  exact hn.trans hlim.le

end SlowEquilibration.SphericalMarkedWindows
