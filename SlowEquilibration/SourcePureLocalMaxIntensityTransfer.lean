-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePurePhysicalIntensityShiftRatio
public import SlowEquilibration.GOEMaximumRelativeLoss

/-! Exponentially accurate transfer of the pure one-point intensity from all
critical points to genuine negative-Hessian local maxima. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEMaximumDeterminant
open Set Filter GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped Topology
set_option maxHeartbeats 400000

/-- The true negative-Hessian determinant mean divided by the ordinary
absolute mean converges to one on every compact exterior shift sequence. -/
theorem maximumMean_div_physicalMean_tendsto_one {b g Z : ℝ}
    (hb : 0 < b) (hg : 0 < g) (k : ℕ → ℝ)
    (hk : ∀ᶠ n : ℕ in atTop, k n ∈ Icc (2*Real.sqrt b+g) Z) :
    Tendsto (fun n : ℕ => maximumMean n (n+2) b (k n)/
      physicalMean n (n+2) b (k n)) atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨C,c,hC,hc,hComp⟩ := maximumMean_relative_comparison (Z := Z) hb hg
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => C*Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.atTop_mul_const hc)
    convert hh.const_mul C using 1
    · funext n
      simp only [Function.comp_def]
      congr 1
      ring
    · ring
  have hErr : Tendsto (fun n : ℕ =>
      maximumMean n (n+2) b (k n)/physicalMean n (n+2) b (k n)-1)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' _ hExp
    filter_upwards [hk,hComp,maximumMean_comparison_eventually (Z := Z) hb hg]
      with n hn hcmp hhalf
    let A := physicalMean n (n+2) b (k n)
    let M := maximumMean n (n+2) b (k n)
    let ε := C*Real.exp (-c*(n+2 : ℕ))
    have hA : 0 < A := physicalMean_pos n 1 hb (by linarith [hn.1])
    have hMupper : M ≤ A := (hhalf (k n) hn).2
    have hCompare : A ≤ (1+ε)*M := hcmp (k n) hn
    have hε : 0 ≤ ε := by dsimp [ε]; positivity
    have hDiff : 0 ≤ A-M := by linarith
    have hLoss : A-M ≤ ε*A := by
      have hmul := mul_le_mul_of_nonneg_left hMupper hε
      nlinarith [hCompare,hmul]
    have hEq : |M/A-1|=(A-M)/A := by
      rw [show M/A-1=(M-A)/A by field_simp]
      rw [abs_div,abs_sub_comm,abs_of_nonneg hDiff,abs_of_pos hA]
    rw [Real.norm_eq_abs,hEq]
    exact (div_le_iff₀ hA).mpr hLoss
  have hh := hErr.add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa only [sub_add_cancel,zero_add] using hh

end SlowEquilibration.GOEMaximumDeterminant

namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory GOEPhysicalPotential GOEPhysicalNormalizedMoments
open GOEMaximumDeterminant SphericalSequentialRegression
open TwoAtomStationarity SphericalTAPCertificate
open scoped Topology ENNReal
set_option maxHeartbeats 500000

/-- At exterior pure energies, the quotient of the two true physical
Kac--Rice densities is exactly the quotient of the two genuine GOE means. -/
theorem pureLocalMaxPhysicalIntensity_div_critical
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (H : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) <
      (p : ℝ)*H/(n+2 : ℕ)) :
    (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal/
      (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal =
        maximumMean n (n+2) (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)
          ((p : ℝ)*H/(n+2 : ℕ)) /
        physicalMean n (n+2) (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)
          ((p : ℝ)*H/(n+2 : ℕ)) := by
  let μ := FiniteMixture.pure p hp a ha
  let b := Q^2*μ.xi2 Q
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hEdge' : 2*Real.sqrt b < (p : ℝ)*(H/(n+2 : ℕ)) := by
    convert hEdge using 1; ring
  have hA : 0 < physicalMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ)) :=
    physicalMean_pos n 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hEdge
  have hM : 0 ≤ maximumMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ)) := by
    unfold maximumMean
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hSphere : 0 < (sphereKRPrefactor (n+1) μ Q).toReal :=
    ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
      (sphereKRPrefactor_ne_top (n+1) μ Q)
  have hPdf : 0 < (physicalValuePdf (n+2) μ Q (H/(n+2 : ℕ))).toReal :=
    physicalValuePdf_toReal_pos (n+2) (by omega) μ hQ _
  unfold pureLocalMaxPhysicalIntensity pureCriticalPhysicalIntensity
    pureNegativeIntensity pureCriticalIntensity
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le)]
  have harg : (p : ℝ)*(H/(n+2 : ℕ))=(p : ℝ)*H/(n+2 : ℕ) := by ring
  rw [harg]
  rw [ENNReal.toReal_ofReal hM,ENNReal.toReal_ofReal hA.le]
  apply (div_eq_div_iff (by positivity) hA.ne').mpr
  ring

/-- The actual local-maximum and all-critical pure physical densities agree
asymptotically at every logarithmically centered source energy. -/
theorem sourcePure_localMaxPhysicalIntensity_div_critical_log_window
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ)) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    Tendsto (fun n : ℕ =>
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal/
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal)
      atTop (𝓝 (1 : ℝ)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let b := Q^2*μ.xi2 Q
  let g := ((p : ℝ)*E-2*Real.sqrt b)/2
  let k : ℕ → ℝ := fun n => (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hg : 0 < g := by dsimp [g]; linarith
  have hLower : 2*Real.sqrt b+g < (p : ℝ)*E := by dsimp [g]; linarith
  have hUpper : (p : ℝ)*E < (p : ℝ)*E+1 := by linarith
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hk : Tendsto k atTop (𝓝 ((p : ℝ)*E)) := by
    have hh := ((tendsto_const_nhds (x := E)).add hσzero).const_mul (p : ℝ)
    convert hh using 1
    · funext n
      dsimp [k]
      field_simp
    · ring
  have hkRange : ∀ᶠ n : ℕ in atTop,
      k n ∈ Icc (2*Real.sqrt b+g) ((p : ℝ)*E+1) := by
    filter_upwards [hk.eventually (Ioi_mem_nhds hLower),
      hk.eventually (Iio_mem_nhds hUpper)] with n hn1 hn2
    exact ⟨hn1.le,hn2.le⟩
  have hMean := maximumMean_div_physicalMean_tendsto_one hb hg k hkRange
  have hEq : (fun n : ℕ =>
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal/
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal)
      =ᶠ[atTop] (fun n : ℕ =>
        maximumMean n (n+2) b (k n)/physicalMean n (n+2) b (k n)) := by
    filter_upwards [hkRange] with n hn
    exact pureLocalMaxPhysicalIntensity_div_critical n p hp a ha
      h.overlap_range.1 _ (by linarith [hn.1])
  exact hMean.congr' hEq.symm

/-- The same source fixed-shift exponential holds for the true
negative-Hessian local-maximum physical density. -/
theorem sourcePure_localMaxPhysicalIntensity_fixed_shift_ratio
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ))
    (t : ℝ) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    Tendsto (fun n : ℕ =>
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal/
        (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal)
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  have hLog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n+2 : ℕ) := by
    have hh : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    exact hh.eventually (eventually_ge_atTop 1)
  have hσt : ∀ᶠ n : ℕ in atTop,
      |σ n+t| ≤ (D+|t|+1)*Real.log (n+2 : ℕ) := by
    filter_upwards [hσ,hLog] with n hn hlog
    have hh := (abs_add_le (σ n) t).trans (add_le_add_left hn |t|)
    nlinarith [abs_nonneg t]
  have hD' : 0 ≤ D+|t|+1 := by positivity
  have hR₁ := sourcePure_localMaxPhysicalIntensity_div_critical_log_window p hp a ha h hD σ hσ
  have hR₂ := sourcePure_localMaxPhysicalIntensity_div_critical_log_window p hp a ha h
    hD' (fun n => σ n+t) hσt
  have hCrit := sourcePure_criticalPhysicalIntensity_fixed_shift_ratio p hp a ha h hD σ hσ t
  have hLim := (hR₂.mul hCrit).div hR₁ one_ne_zero
  have hEq : (fun n : ℕ =>
      ((pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+(σ n+t))).toReal/
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+(σ n+t))).toReal) *
      ((pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal/
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal) /
      ((pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal/
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal))
      =ᶠ[atTop] (fun n : ℕ =>
        (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal/
          (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal) := by
    filter_upwards [hR₁.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hR₂.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn₁ hn₂
    have hC₁ : (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ n)).toReal ≠ 0 := by
      intro hh
      rw [hh,div_zero] at hn₁
      linarith
    have hC₂ : (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+(σ n+t))).toReal ≠ 0 := by
      intro hh
      rw [hh,div_zero] at hn₂
      linarith
    have hL₁ : (pureLocalMaxPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ n)).toReal ≠ 0 := by
      intro hh
      rw [hh,zero_div] at hn₁
      linarith
    have harg : (n+2 : ℕ)*E+(σ n+t)=(n+2 : ℕ)*E+σ n+t := by ring
    rw [harg]
    rw [harg] at hC₂
    field_simp [hC₁,hC₂,hL₁]
  have hLim' := hLim.congr' hEq
  simpa only [one_mul,div_one] using hLim'

end SlowEquilibration.SphericalMarkedWindows
