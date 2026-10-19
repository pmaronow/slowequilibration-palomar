-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureFixedCapEstimates

/-! The literal source deep-energy and angular expectations after division
by their common cap normalizer.  The angular `o(1)` is eliminated by taking
the dimension limsup, and any vanishing coarse-cover deficit is allowed. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCaptureFixedCapEstimates
noncomputable section
open Set Filter MeasureTheory SphericalModel SphericalTAPCertificate
open SphericalPureCapSourceScalars PureStationarity SourceGaussianWindowFraction
open SourceGaussianLaplaceRatio
open scoped ENNReal Topology
set_option autoImplicit false

private theorem real_normalized_le {X : ℝ≥0∞} {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hX : X ≤ ENNReal.ofReal (A*B)) :
    X.toReal/A ≤ B := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  rw [ENNReal.toReal_ofReal (mul_nonneg hA.le hB)] at hh
  exact (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hh)

/-- Source `pc-deep` for an arbitrary vanishing per-spin coarse deficit.
The constant is chosen before the deficit sequence's dimension and every L. -/
theorem FixedCapEstimates.deep_vanishing_deficit
    {p : ℕ} {hp : 4 ≤ p} {β Q a κ δ : ℝ}
    (hEst : FixedCapEstimates p hp β Q a κ δ)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 (0:ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop, ∀ L : ℝ, 0 ≤ L →
      (pureSourceDeepSum p hp β a d
        ((d+2:ℕ)*(pureEnergyConstant p (by omega)-τ d)) L).toReal /
        pureSourceCapMean p hp β a d ≤
      C*Real.exp (-(β*a^p-pureIntensityConstant p (by omega))*L) := by
  obtain ⟨C,hC,hDeep⟩ := hEst.deep
  refine ⟨C,hC,?_⟩
  filter_upwards [hDeep,hEst.mean_eventually_positive,
    hτ.eventually (gt_mem_nhds hEst.deficit_positive)] with d hdeep hA hsmall
  intro L hL
  have hfloor : (d+2:ℕ)*(pureEnergyConstant p (by omega)-δ) ≤
      (d+2:ℕ)*(pureEnergyConstant p (by omega)-τ d) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hh := hdeep L hL _ hfloor
  apply real_normalized_le hA (by positivity)
  convert hh using 1
  congr 1
  ring

/-- The source angular bound with its dimension error removed: each fixed
energy window has one constant independent of the later microscopic width. -/
theorem FixedCapEstimates.angular_limsup
    {p : ℕ} {hp : 4 ≤ p} {β Q a κ δ : ℝ}
    (hEst : FixedCapEstimates p hp β Q a κ δ) :
    ∀ L : ℝ, 0 < L → ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w →
      Filter.limsup (fun d : ℕ =>
        (pureSourceAngularSum p hp β Q a d L w).toReal /
          pureSourceCapMean p hp β a d) atTop ≤
        C*(1-gaussianWindowFraction κ w) := by
  intro L hL
  obtain ⟨C,hC,hAngular⟩ := hEst.angular L hL
  refine ⟨C,hC,?_⟩
  intro w hw
  have hTail : 0 ≤ 1-gaussianWindowFraction κ w :=
    sub_nonneg.mpr (gaussianWindowFraction_le_one hEst.curvature_positive)
  have hCob : IsCoboundedUnder (· ≤ ·) atTop (fun d : ℕ =>
      (pureSourceAngularSum p hp β Q a d L w).toReal /
        pureSourceCapMean p hp β a d) :=
    isCoboundedUnder_le_of_le atTop (fun d =>
      div_nonneg ENNReal.toReal_nonneg (hEst.mean_nonnegative d))
  apply le_of_forall_pos_le_add
  intro ε hε
  have hbound : ∀ᶠ d : ℕ in atTop,
      (pureSourceAngularSum p hp β Q a d L w).toReal /
        pureSourceCapMean p hp β a d ≤ C*(1-gaussianWindowFraction κ w)+ε := by
    filter_upwards [hAngular w hw (ε/C) (div_pos hε hC),
      hEst.mean_eventually_positive] with d hd hA
    have hNormalized :
        (pureSourceAngularSum p hp β Q a d L w).toReal /
          pureSourceCapMean p hp β a d ≤ C*(1-gaussianWindowFraction κ w+ε/C) := by
      apply real_normalized_le hA (by positivity)
      convert hd using 1
      congr 1
      ring
    have heq : C*(1-gaussianWindowFraction κ w+ε/C) =
        C*(1-gaussianWindowFraction κ w)+ε := by
      field_simp [hC.ne']
    exact hNormalized.trans_eq heq
  exact limsup_le_of_le hCob hbound

end
end SlowEquilibration.SourcePureCaptureFixedCapEstimates
