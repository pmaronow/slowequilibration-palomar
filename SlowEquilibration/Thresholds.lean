-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-!
# Scalar threshold calculus for spherical spin mixtures

This file proves the scalar calculus used in equations `eq:pre-Phi-derivative`
and `eq:intro-plateau`, and the elementary threshold ordering in
`rem:pre-thresholds`. The covariance is represented by an actual real function.
The regularity and positivity hypotheses are explicit: this file does not assert
that a stochastic model, Parisi minimizer, or Langevin process has been constructed.
-/

namespace SlowEquilibration.Thresholds

open Set

/-- The dynamical scalar function from `def:pre-thresholds`. -/
noncomputable def A (ξ : ℝ → ℝ) (r : ℝ) : ℝ := (1 - r) * deriv ξ r / r

/-- The replica-symmetric first-variation potential from `def:pre-thresholds`. -/
noncomputable def Phi (ξ : ℝ → ℝ) (β r : ℝ) : ℝ :=
  β ^ 2 * ξ r + r + Real.log (1 - r)

/-- The ratio whose infimum is the square of the static threshold. -/
noncomputable def staticRatio (ξ : ℝ → ℝ) (r : ℝ) : ℝ :=
  (-r - Real.log (1 - r)) / ξ r

/-- The nonnegative dynamical threshold, under the finiteness and positivity
hypotheses in the theorems below. -/
noncomputable def dynamicalThreshold (ξ : ℝ → ℝ) : ℝ :=
  Real.sqrt ((sSup (A ξ '' Ioo 0 1))⁻¹)

/-- The nonnegative static threshold, under the hypotheses in the theorems below. -/
noncomputable def staticThreshold (ξ : ℝ → ℝ) : ℝ :=
  Real.sqrt (sInf (staticRatio ξ '' Ioo 0 1))

/-- Actual derivative of the logarithmic potential. -/
theorem hasDerivAt_Phi {ξ : ℝ → ℝ} {β r : ℝ}
    (hξ : DifferentiableAt ℝ ξ r) (hr : r < 1) :
    HasDerivAt (Phi ξ β) (β ^ 2 * deriv ξ r - r / (1 - r)) r := by
  have hne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  have hlog := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).log hne
  have h := ((hξ.hasDerivAt.const_mul (β ^ 2)).add (hasDerivAt_id r)).add hlog
  convert h using 1
  · ext x
    rfl
  · dsimp
    field_simp [hne]
    ring

/-- Equation `eq:pre-Phi-derivative`, including its factorization through `A`. -/
theorem deriv_Phi {ξ : ℝ → ℝ} {β r : ℝ}
    (hξ : DifferentiableAt ℝ ξ r) (hr : r ∈ Ioo 0 1) :
    deriv (Phi ξ β) r = r / (1 - r) * (β ^ 2 * A ξ r - 1) := by
  rw [(hasDerivAt_Phi hξ hr.2).deriv]
  dsimp [A]
  field_simp [ne_of_gt hr.1, ne_of_gt (sub_pos.mpr hr.2)]

/-- The plateau equation is exactly the equation `β² A(r) = 1`. -/
theorem plateau_iff {ξ : ℝ → ℝ} {β r : ℝ} (hr : r ∈ Ioo 0 1) :
    β ^ 2 * A ξ r = 1 ↔ β ^ 2 * deriv ξ r = r / (1 - r) := by
  dsimp [A]
  constructor <;> intro h
  · field_simp [ne_of_gt hr.1, ne_of_gt (sub_pos.mpr hr.2)] at h ⊢
    nlinarith
  · field_simp [ne_of_gt hr.1, ne_of_gt (sub_pos.mpr hr.2)] at h ⊢
    nlinarith

/-- At an interior differentiability point, a stationary potential solves the
plateau equation. -/
theorem stationary_iff_plateau {ξ : ℝ → ℝ} {β r : ℝ}
    (hξ : DifferentiableAt ℝ ξ r) (hr : r ∈ Ioo 0 1) :
    deriv (Phi ξ β) r = 0 ↔ β ^ 2 * deriv ξ r = r / (1 - r) := by
  rw [(hasDerivAt_Phi hξ hr.2).deriv]
  exact sub_eq_zero

/-- Positivity of the numerator in the static ratio. -/
theorem staticNumerator_pos {r : ℝ} (hr : r ∈ Ioo 0 1) :
    0 < -r - Real.log (1 - r) := by
  have hlog := Real.log_lt_sub_one_of_pos (sub_pos.mpr hr.2)
    (show 1 - r ≠ 1 by linarith [hr.1])
  linarith

/-- A pointwise static-ratio bound is precisely a nonpositive potential. -/
theorem Phi_nonpos_iff {ξ : ℝ → ℝ} {β r : ℝ} (hξ : 0 < ξ r) :
    Phi ξ β r ≤ 0 ↔ β ^ 2 ≤ staticRatio ξ r := by
  rw [staticRatio, le_div_iff₀ hξ]
  dsimp [Phi]
  constructor <;> intro h <;> linarith

/-- Strict version of the pointwise static criterion. -/
theorem Phi_neg_iff {ξ : ℝ → ℝ} {β r : ℝ} (hξ : 0 < ξ r) :
    Phi ξ β r < 0 ↔ β ^ 2 < staticRatio ξ r := by
  rw [staticRatio, lt_div_iff₀ hξ]
  dsimp [Phi]
  constructor <;> intro h <;> linarith

/-- The elementary calculus argument underlying `β_d ≤ β_s`: if `β² A ≤ 1`
on `(0,1)`, the potential cannot increase above its value zero at the origin. -/
theorem Phi_nonpos_of_dynamical_bound {ξ : ℝ → ℝ} {β : ℝ}
    (hξ0 : ξ 0 = 0) (hcont : ContinuousOn ξ (Ico 0 1))
    (hdiff : ∀ r ∈ Ioo 0 1, DifferentiableAt ℝ ξ r)
    (hbound : ∀ r ∈ Ioo 0 1, β ^ 2 * A ξ r ≤ 1) :
    ∀ r ∈ Ioo 0 1, Phi ξ β r ≤ 0 := by
  intro r hr
  have hPhiCont : ContinuousOn (Phi ξ β) (Icc 0 r) := by
    intro y hy
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hr.2
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) y :=
      (continuousAt_const.sub continuousAt_id).log (ne_of_gt (sub_pos.mpr hy1))
    have hξy : ContinuousWithinAt ξ (Icc 0 r) y :=
      (hcont y ⟨hy.1, hy1⟩).mono (fun z hz => ⟨hz.1, lt_of_le_of_lt hz.2 hr.2⟩)
    exact ((hξy.const_mul (β ^ 2)).add
      continuousWithinAt_id).add hlog.continuousWithinAt
  have hanti : AntitoneOn (Phi ξ β) (Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hPhiCont
    · intro y hy
      have hy' : y ∈ Ioo 0 r := by simpa only [interior_Icc] using hy
      exact (hasDerivAt_Phi (hdiff y ⟨hy'.1, lt_trans hy'.2 hr.2⟩)
        (lt_trans hy'.2 hr.2)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : y ∈ Ioo 0 r := by simpa only [interior_Icc] using hy
      have hy01 : y ∈ Ioo 0 1 := ⟨hy'.1, lt_trans hy'.2 hr.2⟩
      rw [deriv_Phi (hdiff y hy01) hy01]
      exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (div_pos hy01.1 (sub_pos.mpr hy01.2)))
        (sub_nonpos.mpr (hbound y hy01))
  have hle := hanti (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.1.le⟩)
    (show r ∈ Icc 0 r from ⟨hr.1.le, le_rfl⟩) hr.1.le
  simpa [Phi, hξ0] using hle

/-- The static ratio is positive whenever the covariance is positive. -/
theorem staticRatio_pos {ξ : ℝ → ℝ} {r : ℝ}
    (hr : r ∈ Ioo 0 1) (hξ : 0 < ξ r) : 0 < staticRatio ξ r :=
  div_pos (staticNumerator_pos hr) hξ

private theorem ratioImage_nonempty (ξ : ℝ → ℝ) :
    (staticRatio ξ '' Ioo 0 1).Nonempty := by
  exact ⟨staticRatio ξ (1 / 2), ⟨1 / 2, by norm_num, rfl⟩⟩

/-- The infimum in the static definition is nonnegative; in particular the
square-root definition has the intended square. -/
theorem staticThreshold_sq {ξ : ℝ → ℝ}
    (hpos : ∀ r ∈ Ioo 0 1, 0 < ξ r) :
    staticThreshold ξ ^ 2 = sInf (staticRatio ξ '' Ioo 0 1) := by
  apply Real.sq_sqrt
  apply le_csInf (ratioImage_nonempty ξ)
  rintro _ ⟨r, hr, rfl⟩
  exact (staticRatio_pos hr (hpos r hr)).le

/-- The scalar replica-symmetric criterion is equivalent to being below the
static threshold. This is only the scalar part of `lem:pre-RS` and makes no
assertion about the Parisi formula or free energy. -/
theorem Phi_nonpos_iff_le_staticThreshold {ξ : ℝ → ℝ} {β : ℝ}
    (hpos : ∀ r ∈ Ioo 0 1, 0 < ξ r) (hβ : 0 ≤ β) :
    (∀ r ∈ Ioo 0 1, Phi ξ β r ≤ 0) ↔ β ≤ staticThreshold ξ := by
  have hbounded : BddBelow (staticRatio ξ '' Ioo 0 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact (staticRatio_pos hr (hpos r hr)).le
  have hinf : (∀ r ∈ Ioo 0 1, β ^ 2 ≤ staticRatio ξ r) ↔
      β ^ 2 ≤ sInf (staticRatio ξ '' Ioo 0 1) := by
    constructor
    · intro h
      apply le_csInf (ratioImage_nonempty ξ)
      rintro _ ⟨r, hr, rfl⟩
      exact h r hr
    · intro h r hr
      exact h.trans (csInf_le hbounded ⟨r, hr, rfl⟩)
  have hpoint : (∀ r ∈ Ioo 0 1, Phi ξ β r ≤ 0) ↔
      (∀ r ∈ Ioo 0 1, β ^ 2 ≤ staticRatio ξ r) := by
    constructor <;> intro h r hr
    · exact (Phi_nonpos_iff (hpos r hr)).mp (h r hr)
    · exact (Phi_nonpos_iff (hpos r hr)).mpr (h r hr)
  rw [hpoint, hinf, ← staticThreshold_sq hpos]
  exact sq_le_sq₀ hβ (Real.sqrt_nonneg _)

/-- Strictly below the static threshold, the scalar potential is strictly
negative throughout `(0,1)`. -/
theorem Phi_neg_of_lt_staticThreshold {ξ : ℝ → ℝ} {β : ℝ}
    (hpos : ∀ r ∈ Ioo 0 1, 0 < ξ r) (hβ : 0 ≤ β)
    (hlt : β < staticThreshold ξ) :
    ∀ r ∈ Ioo 0 1, Phi ξ β r < 0 := by
  have hbounded : BddBelow (staticRatio ξ '' Ioo 0 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact (staticRatio_pos hr (hpos r hr)).le
  have hsq : β ^ 2 < staticThreshold ξ ^ 2 :=
    (sq_lt_sq₀ hβ (Real.sqrt_nonneg _)).mpr hlt
  rw [staticThreshold_sq hpos] at hsq
  intro r hr
  apply (Phi_neg_iff (hpos r hr)).mpr
  exact hsq.trans_le (csInf_le hbounded ⟨r, hr, rfl⟩)

/-- The manuscript's elementary threshold ordering, for every covariance
satisfying the explicit analytic conditions. Finite nonzero mixtures of degrees
at least two satisfy these conditions, but their polynomial construction is
outside this file. -/
theorem dynamicalThreshold_le_staticThreshold {ξ : ℝ → ℝ}
    (hξ0 : ξ 0 = 0) (hcont : ContinuousOn ξ (Ico 0 1))
    (hdiff : ∀ r ∈ Ioo 0 1, DifferentiableAt ℝ ξ r)
    (hpos : ∀ r ∈ Ioo 0 1, 0 < ξ r)
    (hbounded : BddAbove (A ξ '' Ioo 0 1))
    (hApos : ∃ r ∈ Ioo 0 1, 0 < A ξ r) :
    dynamicalThreshold ξ ≤ staticThreshold ξ := by
  obtain ⟨r₀, hr₀, hAr₀⟩ := hApos
  have hM : 0 < sSup (A ξ '' Ioo 0 1) :=
    hAr₀.trans_le (le_csSup hbounded ⟨r₀, hr₀, rfl⟩)
  have hsq : dynamicalThreshold ξ ^ 2 = (sSup (A ξ '' Ioo 0 1))⁻¹ :=
    Real.sq_sqrt (inv_nonneg.mpr hM.le)
  have hbound : ∀ r ∈ Ioo 0 1, dynamicalThreshold ξ ^ 2 * A ξ r ≤ 1 := by
    intro r hr
    rw [hsq]
    calc
      _ ≤ (sSup (A ξ '' Ioo 0 1))⁻¹ * sSup (A ξ '' Ioo 0 1) :=
        mul_le_mul_of_nonneg_left (le_csSup hbounded ⟨r, hr, rfl⟩)
          (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  exact (Phi_nonpos_iff_le_staticThreshold hpos (Real.sqrt_nonneg _)).mp
    (Phi_nonpos_of_dynamical_bound hξ0 hcont hdiff hbound)

/-- The strict superlevel set used in `eq:intro-qstar`. -/
noncomputable def plateauSuperlevel (ξ : ℝ → ℝ) (β : ℝ) : Set ℝ :=
  {r | r ∈ Ioo 0 1 ∧ 1 < β ^ 2 * A ξ r}

/-- The reference plateau is the supremum of the strict superlevel set. -/
noncomputable def qStar (ξ : ℝ → ℝ) (β : ℝ) : ℝ :=
  sSup (plateauSuperlevel ξ β)

/-- The right endpoint of the strict superlevel set lies in `(0,1)` and has
level exactly one. The near-one bound rules out superlevel points approaching
one. This theorem does not assert that the endpoint is the largest root: a
continuous scalar may touch level one again farther to the right. -/
theorem qStar_mem_Ioo_and_level {ξ : ℝ → ℝ} {β : ℝ}
    (hcont : ContinuousOn (A ξ) (Ioo 0 1))
    (hne : (plateauSuperlevel ξ β).Nonempty)
    (hcut : ∃ u < 1, ∀ r ∈ Ioo 0 1, u ≤ r → β ^ 2 * A ξ r ≤ 1) :
    qStar ξ β ∈ Ioo 0 1 ∧ β ^ 2 * A ξ (qStar ξ β) = 1 := by
  obtain ⟨u, hu, hcutoff⟩ := hcut
  have hbdd : BddAbove (plateauSuperlevel ξ β) := by
    refine ⟨u, ?_⟩
    intro r hr
    have hr' : r ∈ Ioo 0 1 ∧ 1 < β ^ 2 * A ξ r := hr
    by_contra hnot
    have hle := hcutoff r hr'.1 (le_of_lt (lt_of_not_ge hnot))
    exact (not_lt_of_ge hle) hr'.2
  have hqle : qStar ξ β ≤ u := by
    apply csSup_le hne
    intro r hr
    have hr' : r ∈ Ioo 0 1 ∧ 1 < β ^ 2 * A ξ r := hr
    by_contra hnot
    exact (not_lt_of_ge (hcutoff r hr'.1 (le_of_lt (lt_of_not_ge hnot)))) hr'.2
  obtain ⟨r₀, hr₀⟩ := hne
  have hr₀' : r₀ ∈ Ioo 0 1 ∧ 1 < β ^ 2 * A ξ r₀ := hr₀
  have hqpos : 0 < qStar ξ β :=
    hr₀'.1.1.trans_le (le_csSup hbdd hr₀)
  have hq : qStar ξ β ∈ Ioo 0 1 := ⟨hqpos, hqle.trans_lt hu⟩
  have hgcont : ContinuousAt (fun r => β ^ 2 * A ξ r) (qStar ξ β) :=
    (hcont.continuousAt (Ioo_mem_nhds hq.1 hq.2)).const_mul (β ^ 2)
  have hqclosure : qStar ξ β ∈ closure (plateauSuperlevel ξ β) :=
    csSup_mem_closure ⟨r₀, hr₀⟩ hbdd
  have himage : (fun r => β ^ 2 * A ξ r) '' plateauSuperlevel ξ β ⊆ Ici 1 := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr.2.le
  have hge : 1 ≤ β ^ 2 * A ξ (qStar ξ β) :=
    closure_minimal himage isClosed_Ici (mem_closure_image hgcont hqclosure)
  have hle : β ^ 2 * A ξ (qStar ξ β) ≤ 1 := by
    by_contra hnot
    have hgt : 1 < β ^ 2 * A ξ (qStar ξ β) := lt_of_not_ge hnot
    have hevent : ∀ᶠ r in nhds (qStar ξ β), r ∈ plateauSuperlevel ξ β :=
      (show ∀ᶠ r in nhds (qStar ξ β), r ∈ Ioo 0 1 from Ioo_mem_nhds hq.1 hq.2).and
        (hgcont.eventually (lt_mem_nhds hgt))
    obtain ⟨l, v, hqv, hsub⟩ := hevent.exists_Ioo_subset
    obtain ⟨r, hqr, hrv⟩ := exists_between hqv.2
    have hrS : r ∈ plateauSuperlevel ξ β := hsub ⟨hqv.1.trans hqr, hrv⟩
    exact (not_lt_of_ge (le_csSup hbdd hrS)) hqr
  exact ⟨hq, le_antisymm hle hge⟩

/-- The actual reference endpoint from `eq:intro-qstar` solves the plateau
equation `eq:intro-plateau`, under the stated continuity and endpoint conditions. -/
theorem qStar_solves_plateau {ξ : ℝ → ℝ} {β : ℝ}
    (hcont : ContinuousOn (A ξ) (Ioo 0 1))
    (hne : (plateauSuperlevel ξ β).Nonempty)
    (hcut : ∃ u < 1, ∀ r ∈ Ioo 0 1, u ≤ r → β ^ 2 * A ξ r ≤ 1) :
    qStar ξ β ∈ Ioo 0 1 ∧
      β ^ 2 * deriv ξ (qStar ξ β) = qStar ξ β / (1 - qStar ξ β) := by
  obtain ⟨hq, hlevel⟩ := qStar_mem_Ioo_and_level hcont hne hcut
  exact ⟨hq, (plateau_iff hq).mp hlevel⟩

/-- For a pure `p`-spin covariance, the dynamical scalar is the polynomial
`p (1-r) r^(p-2)` on its intended domain. -/
theorem A_pure {p : ℕ} (hp : 2 ≤ p) {r : ℝ} (hr : r ≠ 0) :
    A (fun x : ℝ => x ^ p) r = (p : ℝ) * (1 - r) * r ^ (p - 2) := by
  dsimp [A]
  rw [deriv_pow_field]
  have hpow : p - 1 = p - 2 + 1 := by omega
  rw [hpow, pow_succ]
  field_simp

/-- Pure-spin covariances satisfy the analytic hypotheses of the threshold
ordering, without any assumed stochastic theorem. -/
theorem pure_dynamicalThreshold_le_staticThreshold {p : ℕ} (hp : 2 ≤ p) :
    dynamicalThreshold (fun x : ℝ => x ^ p) ≤
      staticThreshold (fun x : ℝ => x ^ p) := by
  apply dynamicalThreshold_le_staticThreshold
  · simp [Nat.ne_zero_of_lt (show 0 < p by omega)]
  · fun_prop
  · intro r hr
    fun_prop
  · intro r hr
    exact pow_pos hr.1 p
  · refine ⟨p, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    rw [A_pure hp (ne_of_gt hr.1)]
    have hpow : r ^ (p - 2) ≤ 1 := pow_le_one₀ hr.1.le hr.2.le
    have hprod : (1 - r) * r ^ (p - 2) ≤ 1 := by
      calc
        _ ≤ 1 * r ^ (p - 2) :=
          mul_le_mul_of_nonneg_right (by linarith [hr.1]) (pow_nonneg hr.1.le _)
        _ = r ^ (p - 2) := one_mul _
        _ ≤ 1 := hpow
    calc
      _ = (p : ℝ) * ((1 - r) * r ^ (p - 2)) := mul_assoc _ _ _
      _ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg p)
      _ = p := mul_one _
  · refine ⟨1 / 2, by norm_num, ?_⟩
    rw [A_pure hp (by norm_num)]
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
    positivity

/-- Derivative of the polynomial that determines a pure-spin dynamical
threshold. The index `n` is `p-2`. -/
theorem hasDerivAt_pureShape {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - x) * x ^ n)
      (r ^ (n - 1) * ((n : ℝ) - ((n : ℝ) + 1) * r)) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).mul
    (hasDerivAt_pow n r)
  convert h using 1
  · ext x
    rfl
  · dsimp
    have hpow : r ^ n = r ^ (n - 1) * r := by
      calc
        r ^ n = r ^ (n - 1 + 1) := congrArg (fun k : ℕ => r ^ k) (by omega)
        _ = r ^ (n - 1) * r := pow_succ r (n - 1)
    rw [hpow]
    ring

/-- The pure-spin shape is maximized at `n/(n+1)` on `[0,1]` for every
`n ≥ 1`, proving the scalar maximizer stated after `eq:intro-plateau`. -/
theorem pureShape_le_at_critical {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : r ∈ Icc 0 1) :
    (1 - r) * r ^ n ≤
      (1 - (n : ℝ) / ((n : ℝ) + 1)) * ((n : ℝ) / ((n : ℝ) + 1)) ^ n := by
  let q : ℝ := (n : ℝ) / ((n : ℝ) + 1)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hqpos : 0 < q := div_pos hnR hden
  have hqlt : q < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  have hqeq : ((n : ℝ) + 1) * q = n := by
    dsimp [q]
    field_simp
  have hmono : MonotoneOn (fun x : ℝ => (1 - x) * x ^ n) (Icc 0 q) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 q)
    · fun_prop
    · intro x hx
      exact (hasDerivAt_pureShape hn x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 q := by simpa only [interior_Icc] using hx
      rw [(hasDerivAt_pureShape hn x).deriv]
      apply mul_nonneg (pow_nonneg hx'.1.le _)
      have hscale := mul_le_mul_of_nonneg_left hx'.2.le hden.le
      linarith
  have hanti : AntitoneOn (fun x : ℝ => (1 - x) * x ^ n) (Icc q 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc q 1)
    · fun_prop
    · intro x hx
      exact (hasDerivAt_pureShape hn x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo q 1 := by simpa only [interior_Icc] using hx
      rw [(hasDerivAt_pureShape hn x).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (hqpos.le.trans hx'.1.le) _)
      have hscale := mul_le_mul_of_nonneg_left hx'.1.le hden.le
      linarith
  by_cases hle : r ≤ q
  · exact hmono ⟨hr.1, hle⟩ ⟨hqpos.le, le_rfl⟩ hle
  · have hge : q ≤ r := (lt_of_not_ge hle).le
    exact hanti ⟨le_rfl, hqlt.le⟩ ⟨hge, hr.2⟩ hge

/-- The pure `p`-spin scalar is maximized at `(p-2)/(p-1)` for all `p ≥ 3`. -/
theorem pure_A_le_at_critical {p : ℕ} (hp : 3 ≤ p) {r : ℝ}
    (hr : r ∈ Ioo 0 1) :
    A (fun x : ℝ => x ^ p) r ≤
      A (fun x : ℝ => x ^ p) (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have hcritPos : (0 : ℝ) < ((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    apply div_pos <;> exact_mod_cast (show 0 < p - _ by omega)
  rw [A_pure (by omega) (ne_of_gt hr.1),
    A_pure (by omega) (ne_of_gt hcritPos)]
  have hshape := pureShape_le_at_critical (n := p - 2) (by omega) ⟨hr.1.le, hr.2.le⟩
  have hden : ((p - 2 : ℕ) : ℝ) + 1 = ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show p - 2 + 1 = p - 1 by omega)
  rw [hden] at hshape
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hshape (Nat.cast_nonneg p)

/-- The supremum of the pure `p`-spin scalar is attained at the stated
critical point for every `p ≥ 3`. -/
theorem pure_A_sup_at_critical {p : ℕ} (hp : 3 ≤ p) :
    sSup (A (fun x : ℝ => x ^ p) '' Ioo 0 1) =
      A (fun x : ℝ => x ^ p) (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have hnum : (0 : ℝ) < (p - 2 : ℕ) := by exact_mod_cast (show 0 < p - 2 by omega)
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hlt : (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_iff₀ hden).mpr
    simp only [one_mul]
    exact_mod_cast (show p - 2 < p - 1 by omega)
  have hcrit : (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) ∈ Ioo 0 1 :=
    ⟨div_pos hnum hden, hlt⟩
  have hmem : A (fun x : ℝ => x ^ p) (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) ∈
      A (fun x : ℝ => x ^ p) '' Ioo 0 1 := ⟨_, hcrit, rfl⟩
  have hbound : BddAbove (A (fun x : ℝ => x ^ p) '' Ioo 0 1) := by
    refine ⟨A (fun x : ℝ => x ^ p) (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)), ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact pure_A_le_at_critical hp hr
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro _ ⟨r, hr, rfl⟩
    exact pure_A_le_at_critical hp hr
  · exact le_csSup hbound hmem

/-- The value of the pure-spin scalar at its critical point. -/
theorem pure_A_at_critical {p : ℕ} (hp : 3 ≤ p) :
    A (fun x : ℝ => x ^ p) (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) =
      (p : ℝ) * ((p - 2 : ℕ) : ℝ) ^ (p - 2) /
        ((p - 1 : ℕ) : ℝ) ^ (p - 1) := by
  have hnum : (0 : ℝ) < (p - 2 : ℕ) := by exact_mod_cast (show 0 < p - 2 by omega)
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  rw [A_pure (by omega) (ne_of_gt (div_pos hnum hden)), div_pow]
  have hn : p - 1 = p - 2 + 1 := by omega
  have hd : ((p - 1 : ℕ) : ℝ) = ((p - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hn
  have hpow : ((p - 1 : ℕ) : ℝ) ^ (p - 1) =
      ((p - 1 : ℕ) : ℝ) ^ (p - 2) * ((p - 1 : ℕ) : ℝ) := by
    calc
      _ = ((p - 1 : ℕ) : ℝ) ^ (p - 2 + 1) :=
        congrArg (fun k : ℕ => ((p - 1 : ℕ) : ℝ) ^ k) hn
      _ = _ := pow_succ _ _
  rw [hpow]
  field_simp [hden.ne']
  rw [hd]
  ring

/-- Exact formula for the pure-spin supremum appearing in the manuscript's
inverse square dynamical threshold. -/
theorem pure_A_sup {p : ℕ} (hp : 3 ≤ p) :
    sSup (A (fun x : ℝ => x ^ p) '' Ioo 0 1) =
      (p : ℝ) * ((p - 2 : ℕ) : ℝ) ^ (p - 2) /
        ((p - 1 : ℕ) : ℝ) ^ (p - 1) := by
  rw [pure_A_sup_at_critical hp, pure_A_at_critical hp]

/-- In the pure cubic case, the maximizer is `1/2` and the maximum is `3/4`. -/
theorem cubic_A_le {r : ℝ} (hr : r ∈ Ioo 0 1) :
    A (fun x : ℝ => x ^ 3) r ≤ 3 / 4 := by
  rw [A_pure (by norm_num) (ne_of_gt hr.1)]
  norm_num
  nlinarith [sq_nonneg (r - 1 / 2)]

/-- The cubic scalar equals its maximum at the interior point `1/2`. -/
theorem cubic_A_at_half : A (fun x : ℝ => x ^ 3) (1 / 2) = 3 / 4 := by
  rw [A_pure (by norm_num) (by norm_num)]
  norm_num

/-- The cubic maximum is uniquely attained at `1/2`. -/
theorem cubic_A_eq_max_iff {r : ℝ} (hr : r ∈ Ioo 0 1) :
    A (fun x : ℝ => x ^ 3) r = 3 / 4 ↔ r = 1 / 2 := by
  rw [A_pure (by norm_num) (ne_of_gt hr.1)]
  norm_num
  constructor
  · intro h
    have hsq : (r - 1 / 2) ^ 2 = 0 := by nlinarith
    nlinarith [sq_nonneg (r - 1 / 2)]
  · intro h
    subst r
    norm_num

/-- The supremum defining the cubic dynamical threshold is exactly `3/4`. -/
theorem cubic_A_sup : sSup (A (fun x : ℝ => x ^ 3) '' Ioo 0 1) = 3 / 4 := by
  have hmem : (3 / 4 : ℝ) ∈ A (fun x : ℝ => x ^ 3) '' Ioo 0 1 :=
    ⟨1 / 2, by norm_num, cubic_A_at_half⟩
  have hbound : BddAbove (A (fun x : ℝ => x ^ 3) '' Ioo 0 1) := by
    refine ⟨3 / 4, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact cubic_A_le hr
  apply le_antisymm
  · apply csSup_le ⟨3 / 4, hmem⟩
    rintro _ ⟨r, hr, rfl⟩
    exact cubic_A_le hr
  · exact le_csSup hbound hmem

/-- Exact cubic dynamical threshold in the manuscript's normalization. -/
theorem cubic_dynamicalThreshold :
    dynamicalThreshold (fun x : ℝ => x ^ 3) = Real.sqrt (4 / 3) := by
  simp only [dynamicalThreshold, cubic_A_sup]
  norm_num

end SlowEquilibration.Thresholds
