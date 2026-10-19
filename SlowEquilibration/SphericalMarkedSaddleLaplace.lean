-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedSaddleQuadratic

/-! The full original source nearby-energy radial normalization, uniformly on
the entire admissible energy band, derived from true physical intensities. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open RadialGaussianBounds RadialLaplaceBounds
open scoped Topology ENNReal
set_option maxHeartbeats 400000

def sourceEnergyRadialDensity (n : ℕ) (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  (mixedLocalMaxPhysicalIntensity n μ Q ((n+2 : ℕ)*e) k).toReal

theorem sourceEnergyRadialDensity_measurable (n : ℕ) (μ : FiniteMixture) (Q e : ℝ) :
    Measurable (sourceEnergyRadialDensity n μ Q e) := by
  unfold sourceEnergyRadialDensity mixedLocalMaxPhysicalIntensity
  apply Measurable.ennreal_toReal
  apply measurable_const.mul
  exact (mixedNegativeIntensity_measurable n μ Q).comp
    (scorePairEquiv.measurable.comp (measurable_const.prodMk measurable_id))

theorem sourceSaddle_density_gaussian_bounds (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ e : ℝ,
      sourceRadialSaddle μ Q e ∈ Ioo L R → ∀ k ∈ Ioo L R,
      c*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)*
        gaussian ((sourceBaselineLowerCurvature μ Q L/2)*(n+2 : ℕ)) (sourceRadialSaddle μ Q e) k ≤
          sourceEnergyRadialDensity n μ Q e k ∧
      sourceEnergyRadialDensity n μ Q e k ≤
        C*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)*
          gaussian ((sourceRadialCurvature μ Q/2)*(n+2 : ℕ)) (sourceRadialSaddle μ Q e) k := by
  let d := (L-sourceRadialEdge μ Q)/2
  have hd : 0 < d := by dsimp [d];linarith
  obtain ⟨c,C,hc,hC,hbound⟩ := mixed_localMax_physical_prefactors μ h.overlap_range.1 hnp (Z := R) hd
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro e hm k hk
  have hkR : k ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+d) R := by
    constructor
    · dsimp [d,sourceRadialEdge] at *
      linarith [hk.1]
    · exact hk.2.le
  have hb := hn e k hkR
  have hfinite := hb.2.1.trans hb.2.2
  have hl := ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt hfinite ENNReal.ofReal_lt_top)) hb.1
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinite
  rw [ENNReal.toReal_ofReal (by positivity)] at hl hu
  rw [←scorePairEquiv_apply] at hl hu
  change c*Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q e k) ≤ sourceEnergyRadialDensity n μ Q e k at hl
  change sourceEnergyRadialDensity n μ Q e k ≤ C*Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q e k) at hu
  have hp := sourceSaddle_profile_bounds μ h hnp hL e hm k hk
  constructor
  · apply le_trans _ hl
    unfold gaussian
    rw [mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (n+2)]
  · apply hu.trans
    unfold gaussian
    rw [mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (n+2)]

/-- Source10.5(b), with constants and dimension threshold before all energies
in the literal source admissible band. -/
theorem sourceSaddle_radial_normalization (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      c*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ) ≤
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*e) ∧
      sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*e) ≤
        C*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ) := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := sourceSaddle_density_gaussian_bounds μ h hnp hL
  let a := sourceRadialCurvature μ Q/2
  let b := sourceBaselineLowerCurvature μ Q L/2
  have hκ := sourceRadialCurvature_pos μ h.overlap_range.1 hnp
  have ha : 0 < a := half_pos hκ
  have hb : 0 < b := by dsimp [b,sourceBaselineLowerCurvature];positivity
  have hu := half_pos (sourceRadialClearance_pos μ hm)
  have hWidth : Tendsto (fun n : ℕ => 1/Real.sqrt (n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))
  refine ⟨lowerConstant c b,upperConstant C a,lowerConstant_pos hc,by
    unfold upperConstant
    exact mul_pos hC (Real.sqrt_pos.mpr (div_pos Real.pi_pos ha)),?_⟩
  filter_upwards [hbounds,hWidth.eventually (gt_mem_nhds hu)] with n hn hwidth
  intro e he
  have hMem := sourceRadialSaddle_mem_of_clearance μ hm (hA4 e he)
  have henv := hn e hMem
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hfi : IntegrableOn (sourceEnergyRadialDensity n μ Q e) (Ioo L R) := by
    apply (((gaussian_integrable (mul_pos ha hN) (sourceRadialSaddle μ Q e)).const_mul
      (C*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e))).restrict).mono'
    · exact (sourceEnergyRadialDensity_measurable n μ Q e).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [Real.norm_of_nonneg (show 0 ≤ sourceEnergyRadialDensity n μ Q e k from ENNReal.toReal_nonneg)]
      exact (henv k hk).2
  have hInside := sourceRadialSaddle_interval_inside μ (hA4 e he) hwidth
  exact ⟨laplace_integral_lower measurableSet_Ioo hfi (fun _ _ => ENNReal.toReal_nonneg)
    hc.le hb.le hN hInside (fun k hk => (henv k (hInside hk)).1),
    laplace_integral_upper measurableSet_Ioo hfi hC.le ha hN (fun k hk => (henv k hk).2)⟩
end SlowEquilibration.SphericalMarkedWindows
