-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSVariation
public import SlowEquilibration.CSFirstVariation
public import SlowEquilibration.MixtureThresholds
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# The actual replica-symmetric Crisanti--Sommers candidate

The measure is the genuine Dirac mass at zero. Its hatted distribution,
functional value and first variation are evaluated from the integral definitions.
The scalar static-threshold criterion is then applied through the proved
Crisanti--Sommers supporting inequality.
-/

namespace SlowEquilibration.CSReplicaSymmetric

open MeasureTheory Set Filter CrisantiSommers
open scoped Topology

/-- A genuinely negative right derivative gives an actual improving point
with probability-mixture weight strictly between zero and one. -/
theorem exists_improvement_of_negative_rightDerivative {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt f d (Icc 0 1) 0) (hdneg : d < 0) :
    ∃ t ∈ Ioo 0 1, f t < f 0 := by
  have htend := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Icc_sdiff_left] at htend
  have hnegative : ∀ᶠ t in 𝓝[Ioc 0 1] 0, slope f 0 t < 0 :=
    htend.eventually (gt_mem_nhds hdneg)
  have hltone : ∀ᶠ t in 𝓝[Ioc (0 : ℝ) 1] 0, t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hdom : ∀ᶠ t in 𝓝[Ioc (0 : ℝ) 1] 0, t ∈ Ioc 0 1 := self_mem_nhdsWithin
  let _ : NeBot (𝓝[Ioc (0 : ℝ) 1] 0) := left_nhdsWithin_Ioc_neBot (by norm_num)
  obtain ⟨t, hneg, hdom, ht1⟩ :=
    (hnegative.and (hdom.and hltone)).exists
  have hquot : (f t - f 0) / t < 0 := by
    simpa only [slope_def_field, sub_zero] using hneg
  have hdiff := (div_lt_iff₀ hdom.1).mp hquot
  exact ⟨t, ⟨hdom.1, ht1⟩, by linarith⟩

/-- The Dirac measure at zero is admissible for every nonnegative cutoff
strictly below one. -/
theorem diracZero_hasCutoff {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasCutoff (Measure.dirac (0 : ℝ)) q := by
  refine ⟨hq0, hq1, ?_⟩
  simp [hq0]

/-- The actual hatted function of the zero atom. -/
theorem xHat_diracZero (t : ℝ) : xHat (Measure.dirac (0 : ℝ)) t = 1 - max t 0 := by
  simp [xHat]

/-- On the physical half-line, the hatted function is exactly `1-t`. -/
theorem xHat_diracZero_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    xHat (Measure.dirac (0 : ℝ)) t = 1 - t := by
  rw [xHat_diracZero, max_eq_left ht]

/-- Exact analytic evaluation of the triangular entropy kernel. -/
theorem integral_triangular_one_sub_sq {s : ℝ} (hs : s ∈ Ico 0 1) :
    (∫ t in (0 : ℝ)..s, (s - t) / (1 - t) ^ 2) = -Real.log (1 - s) - s := by
  have hsne : 1 - s ≠ 0 := (sub_pos.mpr hs.2).ne'
  have hcont : ContinuousOn (fun t : ℝ => (s - t) / (1 - t) ^ 2) (uIcc 0 s) := by
    apply (continuous_const.sub continuous_id).continuousOn.div
      ((continuous_const.sub continuous_id).continuousOn.pow 2)
    intro t ht
    have ht1 : t < 1 := by
      rw [uIcc_of_le hs.1] at ht
      exact ht.2.trans_lt hs.2
    exact pow_ne_zero 2 (sub_pos.mpr ht1).ne'
  have hderiv : ∀ t ∈ uIcc 0 s,
      HasDerivAt (fun t : ℝ => -Real.log (1 - t) - (1 - s) / (1 - t))
        ((s - t) / (1 - t) ^ 2) t := by
    intro t ht
    have ht1 : t < 1 := by
      rw [uIcc_of_le hs.1] at ht
      exact ht.2.trans_lt hs.2
    have hne : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
    have hden := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hlog := (hden.log hne).neg
    have hquot := (hasDerivAt_const t (1 - s)).div hden hne
    convert hlog.sub hquot using 1
    · ext x
      rfl
    · dsimp
      field_simp [hne]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [sub_zero, Real.log_one, neg_zero, div_one, div_self hsne] at h
  linarith

/-- The actual first variation of the zero atom is the scalar potential Phi. -/
theorem firstVariation_diracZero (μ : FiniteMixture) (β : ℝ) {s : ℝ}
    (hs : s ∈ Ico 0 1) :
    firstVariation β μ.xi (Measure.dirac (0 : ℝ)) s = Thresholds.Phi μ.xi β s := by
  have hintegral :
      (∫ t in (0 : ℝ)..s, (s - t) / (xHat (Measure.dirac (0 : ℝ)) t) ^ 2) =
        ∫ t in (0 : ℝ)..s, (s - t) / (1 - t) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs.1] at ht
    dsimp only
    rw [xHat_diracZero_of_nonneg ht.1]
  unfold firstVariation
  rw [hintegral, integral_triangular_one_sub_sq hs]
  unfold Thresholds.Phi
  ring

/-- The actual first variation vanishes at the zero atom. -/
theorem firstVariation_diracZero_zero (μ : FiniteMixture) (β : ℝ) :
    firstVariation β μ.xi (Measure.dirac (0 : ℝ)) 0 = 0 := by
  simp [firstVariation, μ.xi_zero]

/-- The actual functional value of the zero atom is the annealed expression. -/
theorem functional_diracZero (μ : FiniteMixture) (β : ℝ) :
    functional β μ.xi (Measure.dirac (0 : ℝ)) 0 = β ^ 2 * μ.xi 1 / 2 := by
  simp [functional, μ.xi_zero]

/-- The same functional value at every valid cutoff. -/
theorem functional_diracZero_at_cutoff (μ : FiniteMixture) (β : ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    functional β μ.xi (Measure.dirac (0 : ℝ)) q = β ^ 2 * μ.xi 1 / 2 := by
  rw [functional_cutoff_independent (Measure.dirac (0 : ℝ)) β μ.xi
    (diracZero_hasCutoff hq0 hq1) (diracZero_hasCutoff (q := 0) (by norm_num) (by norm_num))]
  exact functional_diracZero μ β

/-- The scalar support condition for the actual first variation is equivalent
to being below the actual static threshold of the canonical finite mixture. -/
theorem firstVariation_nonpos_iff_le_staticThreshold (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) :
    (∀ s ∈ Ico 0 1, firstVariation β μ.xi (Measure.dirac (0 : ℝ)) s ≤ 0) ↔
      β ≤ Thresholds.staticThreshold μ.xi := by
  rw [← μ.Phi_nonpos_iff_le_staticThreshold hβ]
  constructor
  · intro h s hs
    rw [← firstVariation_diracZero μ β ⟨hs.1.le, hs.2⟩]
    exact h s ⟨hs.1.le, hs.2⟩
  · intro h s hs
    by_cases hs0 : s = 0
    · subst s
      rw [firstVariation_diracZero_zero]
    · rw [firstVariation_diracZero μ β hs]
      exact h s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩

/-- The actual almost-everywhere support-on-maximizers condition for the
zero atom is precisely the scalar static-threshold criterion. -/
theorem diracZero_supportCriterion_iff_le_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∀ᵐ s ∂(Measure.dirac (0 : ℝ)),
      ∀ r ∈ Ico 0 1, firstVariation β μ.xi (Measure.dirac (0 : ℝ)) r ≤
        firstVariation β μ.xi (Measure.dirac (0 : ℝ)) s) ↔
      β ≤ Thresholds.staticThreshold μ.xi := by
  simpa [firstVariation_diracZero_zero] using
    firstVariation_nonpos_iff_le_staticThreshold μ hβ

/-- Below the static threshold the actual zero-atom first variation is
strictly negative at every positive overlap. -/
theorem firstVariation_diracZero_neg_of_lt_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) (hlt : β < Thresholds.staticThreshold μ.xi)
    {s : ℝ} (hs : s ∈ Ioo 0 1) :
    firstVariation β μ.xi (Measure.dirac (0 : ℝ)) s < 0 := by
  rw [firstVariation_diracZero μ β ⟨hs.1.le, hs.2⟩]
  exact μ.Phi_neg_of_lt_staticThreshold hβ hlt s hs

/-- In the strict scalar range the actual first-variation zero set consists
only of the origin. -/
theorem firstVariation_diracZero_zeroSet_of_lt_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) (hlt : β < Thresholds.staticThreshold μ.xi) :
    {s | s ∈ Ico 0 1 ∧ firstVariation β μ.xi (Measure.dirac (0 : ℝ)) s = 0} = {0} := by
  ext s
  constructor
  · intro hs
    by_cases hs0 : s = 0
    · exact hs0
    · have hspos : 0 < s := lt_of_le_of_ne hs.1.1 (Ne.symm hs0)
      have hneg := firstVariation_diracZero_neg_of_lt_staticThreshold μ hβ hlt
        ⟨hspos, hs.1.2⟩
      exact False.elim (hneg.ne hs.2)
  · intro hs
    have hs0 : s = 0 := hs
    subst s
    exact ⟨⟨le_rfl, by norm_num⟩, firstVariation_diracZero_zero μ β⟩

/-- The actual first-variation supremum in the replica-symmetric scalar range
is zero and is attained by the Dirac atom. -/
theorem firstVariation_diracZero_sup_of_le_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) (hle : β ≤ Thresholds.staticThreshold μ.xi) :
    sSup (firstVariation β μ.xi (Measure.dirac (0 : ℝ)) '' Ico 0 1) = 0 := by
  have hmax := (firstVariation_nonpos_iff_le_staticThreshold μ hβ).mpr hle
  have hmem : (0 : ℝ) ∈ firstVariation β μ.xi (Measure.dirac (0 : ℝ)) '' Ico 0 1 :=
    ⟨0, ⟨le_rfl, by norm_num⟩, firstVariation_diracZero_zero μ β⟩
  have hbdd : BddAbove (firstVariation β μ.xi (Measure.dirac (0 : ℝ)) '' Ico 0 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hmax s hs
  apply le_antisymm
  · apply csSup_le ⟨0, hmem⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hmax s hs
  · exact le_csSup hbdd hmem

/-- Above the actual static threshold there is a positive first-variation
value at an actual positive overlap, supplying a strictly descending Dirac
mixture direction for the first-variation theorem. -/
theorem exists_firstVariation_diracZero_pos_of_gt_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) (hgt : Thresholds.staticThreshold μ.xi < β) :
    ∃ s ∈ Ioo 0 1, 0 < firstVariation β μ.xi (Measure.dirac (0 : ℝ)) s := by
  have hnot : ¬ (∀ s ∈ Ioo 0 1, Thresholds.Phi μ.xi β s ≤ 0) := by
    intro h
    exact (not_le_of_gt hgt) ((μ.Phi_nonpos_iff_le_staticThreshold hβ).mp h)
  push Not at hnot
  obtain ⟨s, hs, hpos⟩ := hnot
  refine ⟨s, hs, ?_⟩
  rw [firstVariation_diracZero μ β ⟨hs.1.le, hs.2⟩]
  exact hpos

/-- Minimality among all actual probability competitors with a support cutoff
below one. No replica-symmetric classification is included in this definition. -/
def DiracZeroMinimal (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ (ν : Measure ℝ), ∀ (_ : IsProbabilityMeasure ν), ∀ q : ℝ,
    HasCutoff ν q → functional β μ.xi (Measure.dirac (0 : ℝ)) 0 ≤ functional β μ.xi ν q

/-- Sufficient replica-symmetric classification from the actual functional
and its proved supporting inequality. -/
theorem diracZeroMinimal_of_le_staticThreshold (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) (hlt : β ≤ Thresholds.staticThreshold μ.xi) : DiracZeroMinimal μ β := by
  intro ν hν q hq
  let _ : IsProbabilityMeasure ν := hν
  apply functional_minimal_of_firstVariation_maximum β μ.xi ν (Measure.dirac (0 : ℝ))
    hq (diracZero_hasCutoff (by norm_num) (by norm_num))
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt) 0
  · exact (firstVariation_nonpos_iff_le_staticThreshold μ hβ).mpr hlt
  · simp [firstVariation_diracZero_zero]

/-- Every admissible functional value is at least the annealed expression
in the scalar replica-symmetric temperature range. -/
theorem annealed_le_functional_of_le_staticThreshold (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) (hlt : β ≤ Thresholds.staticThreshold μ.xi)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : ℝ} (hq : HasCutoff ν q) :
    β ^ 2 * μ.xi 1 / 2 ≤ functional β μ.xi ν q := by
  rw [← functional_diracZero μ β]
  exact diracZeroMinimal_of_le_staticThreshold μ hβ hlt ν inferInstance q hq

/-- Above the static threshold an explicit admissible mixture of the zero
atom with one positive-overlap atom has strictly smaller actual functional
value than the annealed candidate. The direction and its descent are proved
from the actual first derivative of the functional. -/
theorem exists_improving_two_atom_of_gt_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) (hgt : Thresholds.staticThreshold μ.xi < β) :
    ∃ r ∈ Ioo 0 1, ∃ t ∈ Ioo 0 1,
      IsProbabilityMeasure (mixture (Measure.dirac (0 : ℝ)) (Measure.dirac r) t) ∧
      HasCutoff (mixture (Measure.dirac (0 : ℝ)) (Measure.dirac r) t) r ∧
      functional β μ.xi (mixture (Measure.dirac (0 : ℝ)) (Measure.dirac r) t) r <
        β ^ 2 * μ.xi 1 / 2 := by
  obtain ⟨r, hr, hfpos⟩ := exists_firstVariation_diracZero_pos_of_gt_staticThreshold μ hβ hgt
  have hzeroCut : HasCutoff (Measure.dirac (0 : ℝ)) r := diracZero_hasCutoff hr.1.le hr.2
  have hrCut : HasCutoff (Measure.dirac r) r := by
    refine ⟨hr.1.le, hr.2, ?_⟩
    simp [hr.1.le]
  have hder := functional_mixture_hasDerivWithinAt β μ.xi
    (Measure.dirac (0 : ℝ)) (Measure.dirac r) hzeroCut hrCut
    (fun s _ => (μ.hasDerivAt_xi s).continuousAt.continuousWithinAt)
  simp only [integral_dirac, firstVariation_diracZero_zero] at hder
  have hderneg : (0 - firstVariation β μ.xi (Measure.dirac (0 : ℝ)) r) / 2 < 0 := by
    linarith
  obtain ⟨t, ht, himprove⟩ := exists_improvement_of_negative_rightDerivative hder hderneg
  rw [mixture_zero, functional_diracZero_at_cutoff μ β hr.1.le hr.2] at himprove
  exact ⟨r, hr, t, ht, mixture_isProbability _ _ ⟨ht.1.le, ht.2.le⟩,
    mixture_cutoff _ _ hzeroCut hrCut, himprove⟩

/-- The full actual Dirac-zero minimizer classification: it minimizes the
ordinary Crisanti--Sommers functional exactly up to the static threshold.
The necessary direction is proved by the explicit strictly improving competitor. -/
theorem diracZeroMinimal_iff_le_staticThreshold (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) : DiracZeroMinimal μ β ↔ β ≤ Thresholds.staticThreshold μ.xi := by
  constructor
  · intro hmin
    by_contra hnot
    have hgt : Thresholds.staticThreshold μ.xi < β := lt_of_not_ge hnot
    obtain ⟨r, hr, t, ht, hprob, hcut, himprove⟩ :=
      exists_improving_two_atom_of_gt_staticThreshold μ hβ hgt
    have hle := hmin (mixture (Measure.dirac (0 : ℝ)) (Measure.dirac r) t) hprob r hcut
    rw [functional_diracZero μ β] at hle
    exact (not_lt_of_ge hle) himprove
  · exact diracZeroMinimal_of_le_staticThreshold μ hβ

end SlowEquilibration.CSReplicaSymmetric
