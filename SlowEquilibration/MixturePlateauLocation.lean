-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureThresholds
public import SlowEquilibration.SphericalLatitudeCovariance

@[expose] public section

/-!
# Genuine plateau location and latitude parameter bounds

The endpoint is the supremum of the strict dynamical superlevel set. Its
degree-dependent location follows from actual monomial derivatives; no
largest-root or plateau-location hypothesis is imposed.
-/

namespace SlowEquilibration.FiniteMixture

noncomputable section
open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Critical overlap associated with a lower supported degree. -/
def degreeCriticalOverlap (d : ℕ) : ℝ := ((d : ℝ)-2)/((d : ℝ)-1)

theorem degreeCriticalOverlap_mem_Ioo {d : ℕ} (hd : 3 ≤ d) :
    degreeCriticalOverlap d ∈ Ioo (0 : ℝ) 1 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold degreeCriticalOverlap
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  exact (div_lt_one (by linarith : (0 : ℝ) < d-1)).mpr (by linarith)

/-- Every supported pure shape is increasing up to the critical overlap
of the actual lower degree bound. -/
theorem pureShape_monotoneOn_of_degree {d p : ℕ} (hd : 3 ≤ d) (hp : d ≤ p) :
    MonotoneOn (fun r : ℝ => (1-r)*r^(p-2))
      (Icc (0 : ℝ) (degreeCriticalOverlap d)) := by
  let q := degreeCriticalOverlap d
  have hq := degreeCriticalOverlap_mem_Ioo hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpR : (d : ℝ) ≤ p := by exact_mod_cast hp
  have hqeq : ((d : ℝ)-1)*q = (d : ℝ)-2 := by
    dsimp [q, degreeCriticalOverlap]
    field_simp [show (d : ℝ)-1 ≠ 0 by linarith]
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 q)
  · fun_prop
  · intro r hr
    exact (Thresholds.hasDerivAt_pureShape (n := p-2) (by omega) r).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) q := by simpa only [interior_Icc] using hr
    rw [(Thresholds.hasDerivAt_pureShape (n := p-2) (by omega) r).deriv]
    apply mul_nonneg (pow_nonneg hr'.1.le _)
    have hp2 : ((p-2 : ℕ) : ℝ) = (p : ℝ)-2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ p)]
      norm_num
    rw [hp2]
    have hprod := mul_nonneg (sub_nonneg.mpr hpR) (sub_pos.mpr hq.2).le
    have hscale := mul_le_mul_of_nonneg_left hr'.2.le (by linarith : (0 : ℝ) ≤ p-1)
    nlinarith

/-- The true dynamical scalar is increasing up to the lower-degree
critical overlap, even with mixed parities and zero coefficients. -/
theorem A_monotoneOn_before_degreeCritical (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegree : d ≤ μ.minDegree) :
    MonotoneOn (Thresholds.A μ.xi) (Ioc (0 : ℝ) (degreeCriticalOverlap d)) := by
  intro r hr s hs hrs
  rw [μ.A_eq_polynomial hr.1.ne', μ.A_eq_polynomial hs.1.ne']
  apply Finset.sum_le_sum
  intro p hp
  have hdP : d ≤ p := hdegree.trans (μ.degree_bounds hp).1
  have hmono := pureShape_monotoneOn_of_degree hd hdP ⟨hr.1.le, hr.2⟩ ⟨hs.1.le, hs.2⟩ hrs
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmono (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))

/-- The strict superlevel defining the genuine plateau endpoint is bounded
above by one, directly from its literal domain. -/
theorem plateauSuperlevel_bddAbove (μ : FiniteMixture) (β : ℝ) :
    BddAbove (Thresholds.plateauSuperlevel μ.xi β) :=
  ⟨1, fun _r hr => hr.1.2.le⟩

/-- Every point to the right of the actual plateau endpoint is below or
at level one. Tangencies farther right are allowed. -/
theorem A_le_one_of_qStar_lt (μ : FiniteMixture) {β r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hqr : Thresholds.qStar μ.xi β < r) :
    β^2*Thresholds.A μ.xi r ≤ 1 := by
  by_contra hn
  have hm : r ∈ Thresholds.plateauSuperlevel μ.xi β := ⟨hr, lt_of_not_ge hn⟩
  exact (not_lt_of_ge (le_csSup (μ.plateauSuperlevel_bddAbove β) hm)) hqr

/-- Above the genuine dynamical threshold, the actual plateau endpoint lies
strictly to the right of the lower-degree critical overlap. -/
theorem degreeCriticalOverlap_lt_qStar (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegree : d ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    degreeCriticalOverlap d < Thresholds.qStar μ.xi β := by
  let q := degreeCriticalOverlap d
  have hq := degreeCriticalOverlap_mem_Ioo hd
  obtain ⟨r, hr⟩ := μ.plateauSuperlevel_nonempty hβ
  by_cases hqr : q < r
  · exact hqr.trans_le (le_csSup (μ.plateauSuperlevel_bddAbove β) hr)
  · have hrq : r ≤ q := le_of_not_gt hqr
    have hmono := μ.A_monotoneOn_before_degreeCritical hd hdegree
      ⟨hr.1.1, hrq⟩ ⟨hq.1, le_rfl⟩ hrq
    have hqlevel : 1 < β^2*Thresholds.A μ.xi q :=
      hr.2.trans_le (mul_le_mul_of_nonneg_left hmono (sq_nonneg β))
    have hcont : ContinuousAt (fun s => β^2*Thresholds.A μ.xi s) q :=
      (μ.continuousAt_A hq.1.ne').const_mul _
    have hev : ∀ᶠ s in 𝓝 q, s ∈ Thresholds.plateauSuperlevel μ.xi β :=
      (show ∀ᶠ s in 𝓝 q, s ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hq.1 hq.2).and
        (hcont.eventually (lt_mem_nhds hqlevel))
    obtain ⟨l, u, hlu, hsub⟩ := hev.exists_Ioo_subset
    obtain ⟨s, hqs, hsu⟩ := exists_between hlu.2
    exact hqs.trans_le (le_csSup (μ.plateauSuperlevel_bddAbove β)
      (hsub ⟨hlu.1.trans hqs, hsu⟩))

/-- Minimum degree at least three supplies the literal latitude lower
bound required by the odd-mixture covariance comparison. -/
theorem half_lt_qStar (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    (1/2 : ℝ) < Thresholds.qStar μ.xi β := by
  have h := μ.degreeCriticalOverlap_lt_qStar (d := 3) (by omega) hd hβ
  norm_num [degreeCriticalOverlap] at h
  exact h

/-- For minimum degree at least four, the actual plateau lies strictly
above two thirds, leaving a genuine margin for a nearby latitude. -/
theorem two_thirds_lt_qStar (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    (2/3 : ℝ) < Thresholds.qStar μ.xi β := by
  have h := μ.degreeCriticalOverlap_lt_qStar (d := 4) (by omega) hd hβ
  norm_num [degreeCriticalOverlap] at h
  exact h

/-- Tangent support at the literal genuine plateau latitude, including odd
degrees, with every needed latitude bound derived from the actual mixture. -/
theorem xi_qStar_latitude_tangent_le (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β t : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    let q := Thresholds.qStar μ.xi β
    μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t) := by
  have hq := (μ.qStar_solves_plateau hβ).1
  exact μ.xi_latitude_tangent_le ⟨(μ.half_lt_qStar hd hβ).le, hq.2.le⟩ ht

/-- Every larger physical latitude inherits the true tangent-support
condition from the proved plateau degree bound. -/
theorem xi_latitude_tangent_le_of_qStar_le (μ : FiniteMixture)
    (hd : 3 ≤ μ.minDegree) {β q t : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hq : Thresholds.qStar μ.xi β ≤ q) (hq1 : q ≤ 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t) :=
  μ.xi_latitude_tangent_le ⟨((μ.half_lt_qStar hd hβ).trans_le hq).le, hq1⟩ ht

/-- A genuine positive plateau margin permits the slightly smaller
latitude `qStar-ε/2` used in the cap construction. -/
theorem exists_qStar_latitude_margin (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ico (0 : ℝ) δ,
      Thresholds.qStar μ.xi β-ε/2 ∈ Ioo (1/2 : ℝ) 1 := by
  have hhalf := μ.half_lt_qStar hd hβ
  have hq1 := (μ.qStar_solves_plateau hβ).1.2
  refine ⟨2*(Thresholds.qStar μ.xi β-1/2), by linarith, ?_⟩
  intro ε hε
  constructor <;> linarith [hε.1, hε.2]

end

end SlowEquilibration.FiniteMixture
