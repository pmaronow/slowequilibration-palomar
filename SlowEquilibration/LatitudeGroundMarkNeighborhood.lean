-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundTrialGap

/-! Genuine uniform near-ground mark neighborhoods. Bounds are obtained
from the literal source regression coefficients on a fixed compact latitude
interval; no desired continuity or mean perturbation bound is a premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open Set SphericalParisiConditionedLatitudeCovariance
open SphericalSequentialRegression SphericalCriticalLatitude SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem sourceMean_affine (μ : FiniteMixture) (Q e k r : ℝ) :
    sourceConditionalMean μ Q e k r=
      e*sourceConditionalMean μ Q 1 0 r+k*sourceConditionalMean μ Q 0 1 r := by
  simp only [sourceConditionalMean,sourceCross,scorePairEquiv_apply,
    dotProduct,Matrix.mulVec,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem sourceMean_continuous (μ : FiniteMixture) (Q e k : ℝ) :
    Continuous (sourceConditionalMean μ Q e k) := by
  have hξ : Continuous μ.xi := continuous_iff_continuousAt.mpr
    (fun t => (μ.hasDerivAt_xi t).continuousAt)
  have hξ1 : Continuous μ.xi1 := continuous_iff_continuousAt.mpr
    (fun t => (μ.hasDerivAt_xi1 t).continuousAt)
  unfold sourceConditionalMean sourceCross
  simp only [scorePairEquiv_apply,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
  unfold centerCovariance centerFirst
  fun_prop

theorem sourceMean_uniform_coefficient_bound (μ : FiniteMixture) (Q ε η : ℝ)
    (hεη : ε ≤ 1-η) :
    ∃ C > 0, ∀ r ∈ Icc ε (1-η),
      |sourceConditionalMean μ Q 1 0 r|+|sourceConditionalMean μ Q 0 1 r| ≤ C := by
  let f := fun r => |sourceConditionalMean μ Q 1 0 r|+|sourceConditionalMean μ Q 0 1 r|
  have hf : Continuous f := (sourceMean_continuous μ Q 1 0).abs.add
    (sourceMean_continuous μ Q 0 1).abs
  obtain ⟨r₀,_hr₀,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc ε (1-η)).Nonempty from ⟨ε,le_rfl,hεη⟩) hf.continuousOn
  refine ⟨f r₀+1,by dsimp [f]; positivity,?_⟩
  intro r hr
  exact (hmax hr).trans (by linarith)

theorem sourceMean_mark_variation (μ : FiniteMixture) (Q E K e k r C ρ : ℝ)
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hbound : |sourceConditionalMean μ Q 1 0 r|+|sourceConditionalMean μ Q 0 1 r| ≤ C)
    (he : |e-E| ≤ ρ) (hk : |k-K| ≤ ρ) :
    |sourceConditionalMean μ Q e k r-sourceConditionalMean μ Q E K r| ≤ ρ*C := by
  have hEq : sourceConditionalMean μ Q e k r-sourceConditionalMean μ Q E K r=
      (e-E)*sourceConditionalMean μ Q 1 0 r+(k-K)*sourceConditionalMean μ Q 0 1 r := by
    rw [sourceMean_affine μ Q e k r,sourceMean_affine μ Q E K r]
    ring
  rw [hEq]
  calc
    _ ≤ |(e-E)*sourceConditionalMean μ Q 1 0 r| + |(k-K)*sourceConditionalMean μ Q 0 1 r| := abs_add_le _ _
    _ = |e-E| * |sourceConditionalMean μ Q 1 0 r| + |k-K| * |sourceConditionalMean μ Q 0 1 r| := by rw [abs_mul,abs_mul]
    _ ≤ ρ * |sourceConditionalMean μ Q 1 0 r| + ρ * |sourceConditionalMean μ Q 0 1 r| :=
      add_le_add (mul_le_mul_of_nonneg_right he (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hk (abs_nonneg _))
    _ ≤ ρ*C := by rw [←mul_add];exact mul_le_mul_of_nonneg_left hbound hρ

theorem exists_uniform_source_mean_neighborhood (μ : FiniteMixture)
    (Q E K ε η a₀ b₀ : ℝ) (hεη : ε ≤ 1-η) (ha : a₀ < K) (hb : K < b₀)
    {δMax τ : ℝ} (hδMax : 0 < δMax) (hτ : 0 < τ) :
    ∃ L R δ : ℝ, L < K ∧ K < R ∧ Icc L R ⊆ Ioo a₀ b₀ ∧
      0 < δ ∧ δ ≤ δMax ∧
      ∀ r ∈ Icc ε (1-η), ∀ e ∈ Icc (E-δ) (E+δ), ∀ k ∈ Icc L R,
        |sourceConditionalMean μ Q e k r-sourceConditionalMean μ Q E K r| ≤ τ := by
  obtain ⟨C,hC,hbound⟩ := sourceMean_uniform_coefficient_bound μ Q ε η hεη
  let ρ := τ/C
  have hρ : 0 < ρ := div_pos hτ hC
  let w := min ((K-a₀)/2) (min ((b₀-K)/2) ρ)
  have hw : 0 < w := lt_min (by linarith) (lt_min (by linarith) hρ)
  have hwa : w ≤ (K-a₀)/2 := min_le_left _ _
  have hwb : w ≤ (b₀-K)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hwρ : w ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
  let δ := min δMax ρ
  have hδ : 0 < δ := lt_min hδMax hρ
  refine ⟨K-w,K+w,δ,by linarith,by linarith,?_,hδ,min_le_left _ _,?_⟩
  · intro k hk
    constructor <;> linarith [hk.1,hk.2]
  · intro r hr e he k hk
    have heρ : |e-E| ≤ ρ := (abs_le.mpr (by constructor <;> linarith [he.1,he.2])).trans
      (min_le_right δMax ρ)
    have hkρ : |k-K| ≤ ρ := (abs_le.mpr (by constructor <;> linarith [hk.1,hk.2])).trans hwρ
    have H := sourceMean_mark_variation μ Q E K e k r C ρ hC.le hρ.le (hbound r hr) heρ hkρ
    have hcancel : ρ*C=τ := div_mul_cancel₀ τ hC.ne'
    rwa [hcancel] at H

theorem exists_mixed_uniform_trial_gap (μ : FiniteMixture) {β x Q ε η a₀ b₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η)
    (ha : a₀ < markK μ β Q) (hb : markK μ β Q < b₀)
    {δMax : ℝ} (hδMax : 0 < δMax) :
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    ∃ L R δ : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc L R ⊆ Ioo a₀ b₀ ∧ 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧
      ∀ r ∈ Icc ε (1-η), ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
        ∀ k ∈ Icc L R,
        sourceConditionalMean μ Q e k r+
          functional (centeredFirst μ Q r) (centeredSecond μ Q r)
            (height (markY β Q) (markZ x Q) r) (markZ x Q/markY β Q) (location r) ≤
          markE μ β x Q-7*G/8 := by
  dsimp only
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  obtain ⟨hG,htrial⟩ := source_trial_gap μ h hnp hε hη hεη
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδsmall,hvariation⟩ :=
    exists_uniform_source_mean_neighborhood μ Q (markE μ β x Q) (markK μ β Q)
      ε η a₀ b₀ hεη.le ha hb
      (δMax := min δMax (G/8)) (τ := G/8)
      (lt_min hδMax (by dsimp [G];positivity)) (by dsimp [G];positivity)
  have hδG : δ ≤ G/8 := hδsmall.trans (min_le_right _ _)
  refine ⟨L,R,δ,hL,hR,hsub,hδ,by linarith,hδsmall.trans (min_le_left _ _),?_⟩
  intro r hr e he k hk
  have hv := (abs_le.mp (hvariation r hr e he k hk)).2
  have ht := htrial r hr
  change sourceConditionalMean μ Q (markE μ β x Q) (markK μ β Q) r+
    functional (centeredFirst μ Q r) (centeredSecond μ Q r)
      (height (markY β Q) (markZ x Q) r) (markZ x Q/markY β Q) (location r) ≤
    markE μ β x Q-G at ht
  linarith

end SlowEquilibration.LatitudeGroundTrial
