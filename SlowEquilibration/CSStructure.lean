-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSFirstVariation
public import SlowEquilibration.CSCalculus
public import SlowEquilibration.CSReplicaSymmetric
public import SlowEquilibration.ContactGeometry
public import SlowEquilibration.InverseSqrtCalculus
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Geometry of actual Crisanti--Sommers minimizers

This module works with the ordinary admissible probability measures and their
actual integral first variations. Support extrema are obtained from the compact
topological measure support; origin membership and contact-count conclusions
are derived rather than supplied as structural premises.
-/

namespace SlowEquilibration.CSStructure

open MeasureTheory Set Filter CrisantiSommers
open scoped Topology

/-- A finite mixture of minimum supported degree at least three satisfies the
strict derivative gap used to exclude a positive first support point. -/
theorem degree_gap (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree) {r : ℝ} (hr : 0 < r) :
    μ.xi1 r < r * μ.xi2 r := by
  unfold FiniteMixture.xi1 FiniteMixture.xi2
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro p hp
    have hp3 : 3 ≤ p := hd.trans (μ.degree_bounds hp).1
    have hpow : p - 1 = p - 2 + 1 := by omega
    rw [hpow, pow_succ]
    unfold FiniteMixture.curvatureCoeff
    have hnonneg : 0 ≤ μ.coeff p * (p : ℝ) * r ^ (p - 2) * r := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
        (pow_nonneg hr.le _)) hr.le
    have hfactor : (1 : ℝ) ≤ (p - 1 : ℕ) := by exact_mod_cast (show 1 ≤ p - 1 by omega)
    nlinarith
  · obtain ⟨p, hp⟩ := μ.support_nonempty
    refine ⟨p, hp, ?_⟩
    have hp3 : 3 ≤ p := hd.trans (μ.degree_bounds hp).1
    have hpow : p - 1 = p - 2 + 1 := by omega
    rw [hpow, pow_succ]
    unfold FiniteMixture.curvatureCoeff
    have hpositive : 0 < μ.coeff p * (p : ℝ) * r ^ (p - 2) * r := by
      exact mul_pos (mul_pos (mul_pos (μ.coeff_pos hp)
        (Nat.cast_pos.mpr (by omega))) (pow_pos hr _)) hr
    have hfactor : (1 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 1 < p - 1 by omega)
    nlinarith

/-- The actual support is contained in its closed cutoff interval. -/
theorem support_subset_cutoff (ζ : Measure ℝ) {q : ℝ} (hq : HasCutoff ζ q) :
    ζ.support ⊆ Icc 0 q :=
  ζ.support_subset_of_isClosed isClosed_Icc hq.2.2

/-- Every admissible probability law has a genuine first support point. -/
theorem exists_first_support_point (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) :
    ∃ a ∈ ζ.support, a ∈ Icc 0 q ∧ ∀ r ∈ ζ.support, a ≤ r := by
  have hsub := support_subset_cutoff ζ hq
  have hcompact : IsCompact ζ.support :=
    isCompact_Icc.of_isClosed_subset ζ.isClosed_support hsub
  have hnonempty : ζ.support.Nonempty := ζ.nonempty_support (IsProbabilityMeasure.ne_zero ζ)
  obtain ⟨a, ha, hmin⟩ := hcompact.exists_isMinOn hnonempty continuous_id.continuousOn
  exact ⟨a, ha, hsub ha, hmin⟩

/-- Almost-everywhere support lower bounds force the actual hatted function
to be constant throughout the entire half-line below that bound. -/
theorem xHat_constant_below_ae_lower_bound (ζ : Measure ℝ) {a t : ℝ}
    (ha : ∀ᵐ r ∂ζ, a ≤ r) (ht : t ≤ a) : xHat ζ t = xHat ζ a := by
  unfold xHat
  apply integral_congr_ae
  filter_upwards [ha] with r hr
  rw [max_eq_right (ht.trans hr), max_eq_right hr]

/-- In particular, the actual hatted function is constant below the first
topological support point, using the conullness of that support. -/
theorem xHat_constant_below_first_support (ζ : Measure ℝ) {a t : ℝ}
    (hmin : ∀ r ∈ ζ.support, a ≤ r) (ht : t ≤ a) : xHat ζ t = xHat ζ a :=
  by
    have hsupp : ∀ᵐ r ∂ζ, r ∈ ζ.support := ζ.support_mem_ae
    exact xHat_constant_below_ae_lower_bound ζ (hsupp.mono (fun r hr => hmin r hr)) ht

/-- Continuous almost-everywhere equality on a closed cutoff interval holds
at every point of the actual topological support. -/
theorem eq_on_support_of_ae_eq (ζ : Measure ℝ) {q : ℝ} (hq : HasCutoff ζ q)
    {f : ℝ → ℝ} {m : ℝ} (hf : ContinuousOn f (Icc 0 q))
    (heq : ∀ᵐ r ∂ζ, f r = m) {a : ℝ} (ha : a ∈ ζ.support) : f a = m := by
  have hclosed : IsClosed (Icc 0 q ∩ f ⁻¹' {m}) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hae : Icc 0 q ∩ f ⁻¹' {m} ∈ ae ζ := by
    filter_upwards [hq.2.2, heq] with r hr hf
    exact ⟨hr, hf⟩
  exact (ζ.support_subset_of_isClosed hclosed hae ha).2

/-- A strictly positive first support point would make the actual second
first-variation derivative positive once its first derivative vanishes.
This scalar contradiction is used with the proved global-maximality condition. -/
theorem positive_first_support_curvature_contradiction
    {β a C u v : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hgap : u < a * v) (hstationary : β ^ 2 * u - a / C ^ 2 = 0)
    (hsecond : β ^ 2 * v - 1 / C ^ 2 ≤ 0) : False := by
  have hscaled := mul_lt_mul_of_pos_left hgap (sq_pos_of_pos hβ)
  have hsec := mul_le_mul_of_nonneg_left (sub_nonpos.mp hsecond) ha.le
  have heq : β ^ 2 * u = a / C ^ 2 := sub_eq_zero.mp hstationary
  have hbound : β ^ 2 * (a * v) ≤ a / C ^ 2 := by
    calc
      _ = a * (β ^ 2 * v) := by ring
      _ ≤ a * (1 / C ^ 2) := hsec
      _ = a / C ^ 2 := by ring
  rw [heq] at hscaled
  exact (not_lt_of_ge hbound) hscaled

private theorem hasDerivAt_deriv_xi (μ : FiniteMixture) (r : ℝ) :
    HasDerivAt (deriv μ.xi) (μ.xi2 r) r := by
  have heq : deriv μ.xi = μ.xi1 := funext (fun t => (μ.hasDerivAt_xi t).deriv)
  rw [heq]
  exact μ.hasDerivAt_xi1 r

private theorem differentiableOn_xi (μ : FiniteMixture) :
    DifferentiableOn ℝ μ.xi (Iio 1) :=
  fun r _ => (μ.hasDerivAt_xi r).differentiableAt.differentiableWithinAt

private theorem firstVariation_continuousOn_cutoff (μ : FiniteMixture) (β : ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {q : ℝ} (hq : HasCutoff ζ q) :
    ContinuousOn (firstVariation β μ.xi ζ) (Icc 0 q) := by
  intro r hr
  exact (firstVariation_hasDerivAt β μ.xi ζ hq (hr.2.trans_lt hq.2.1)
    (μ.hasDerivAt_xi r)).continuousAt.continuousWithinAt

/-- Genuine minimizers of a covariance of minimum degree at least three
have the origin in their actual topological support. The positive-first-support
alternative is excluded by the first and second derivative tests. -/
theorem origin_mem_support_of_minimizer (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) :
    (0 : ℝ) ∈ ζ.law.support := by
  have hξcont : ContinuousOn μ.xi (Ico 0 1) :=
    fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  obtain ⟨m, hmax, hsupport⟩ := (ζ.minimizer_iff_support_on_maximum β μ.xi hξcont).mp hmin
  obtain ⟨a, ha, harange, hfirst⟩ := exists_first_support_point ζ.law ζ.hasCutoff
  have hfa : firstVariation β μ.xi ζ.law a = m :=
    eq_on_support_of_ae_eq ζ.law ζ.hasCutoff
      (firstVariation_continuousOn_cutoff μ β ζ.law ζ.hasCutoff) hsupport ha
  have ha0 : a = 0 := by
    by_contra hane
    have hapos : 0 < a := lt_of_le_of_ne harange.1 (Ne.symm hane)
    have ha1 : a < 1 := harange.2.trans_lt ζ.hasCutoff.2.1
    have hlocal : IsLocalMax (firstVariation β μ.xi ζ.law) a := by
      filter_upwards [Ioo_mem_nhds hapos ha1] with r hr
      rw [hfa]
      exact hmax r ⟨hr.1.le, hr.2⟩
    have hstationary := hlocal.deriv_eq_zero
    rw [firstVariation_deriv β μ.xi ζ.law ζ.hasCutoff ha1
      (μ.hasDerivAt_xi a).differentiableAt, (μ.hasDerivAt_xi a).deriv] at hstationary
    have hint : (∫ t in (0 : ℝ)..a, 1 / (xHat ζ.law t) ^ 2) =
        a / (xHat ζ.law a) ^ 2 := by
      calc
        _ = ∫ t in (0 : ℝ)..a, 1 / (xHat ζ.law a) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hapos.le] at ht
          dsimp only
          rw [xHat_constant_below_first_support ζ.law hfirst ht.2]
        _ = _ := by simp; ring
    rw [hint] at hstationary
    have hφcont := (firstVariation_hasDerivAt β μ.xi ζ.law ζ.hasCutoff ha1
      (μ.hasDerivAt_xi a)).continuousAt
    have hnonneg := ContactGeometry.deriv2_nonneg_of_isLocalMin hlocal.neg hφcont.neg
    have hsecond : deriv (deriv (firstVariation β μ.xi ζ.law)) a ≤ 0 := by
      have hnegfun : deriv (fun r => -firstVariation β μ.xi ζ.law r) =
          (fun r => -deriv (firstVariation β μ.xi ζ.law) r) := by
        ext r
        exact deriv.neg
      rw [hnegfun] at hnonneg
      have hneg2 : deriv (fun r => -deriv (firstVariation β μ.xi ζ.law) r) a =
          -deriv (deriv (firstVariation β μ.xi ζ.law)) a := deriv.neg
      rw [hneg2] at hnonneg
      exact neg_nonneg.mp hnonneg
    rw [(firstVariation_deriv_hasDerivAt β μ.xi ζ.law ζ.hasCutoff ha1
      (differentiableOn_xi μ) (hasDerivAt_deriv_xi μ a)).deriv] at hsecond
    exact positive_first_support_curvature_contradiction hβ hapos
      (degree_gap μ hd hapos) hstationary hsecond
  simpa [ha0] using ha

/-- Once origin membership has been derived, the global first-variation
maximum of an actual minimizer is zero, including equality on all support points. -/
theorem minimizer_firstVariation_maximum_zero (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) :
    (∀ r ∈ Ico 0 1, firstVariation β μ.xi ζ.law r ≤ 0) ∧
    (∀ᵐ r ∂ζ.law, firstVariation β μ.xi ζ.law r = 0) ∧
    (∀ r ∈ ζ.law.support, firstVariation β μ.xi ζ.law r = 0) := by
  have hξcont : ContinuousOn μ.xi (Ico 0 1) :=
    fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  obtain ⟨m, hmax, hsupport⟩ := (ζ.minimizer_iff_support_on_maximum β μ.xi hξcont).mp hmin
  have hclosed := firstVariation_continuousOn_cutoff μ β ζ.law ζ.hasCutoff
  have h0eq := eq_on_support_of_ae_eq ζ.law ζ.hasCutoff hclosed hsupport
    (origin_mem_support_of_minimizer μ hd hβ ζ hmin)
  have hm0 : m = 0 := by simpa [firstVariation, μ.xi_zero] using h0eq.symm
  rw [hm0] at hmax hsupport
  exact ⟨hmax, hsupport,
    fun r hr => eq_on_support_of_ae_eq ζ.law ζ.hasCutoff hclosed hsupport hr⟩

/-- The actual comparator whose zeros are the first-variation curvature zeros. -/
noncomputable def comparator (μ : FiniteMixture) (β : ℝ) (ζ : Measure ℝ) (r : ℝ) : ℝ :=
  InverseSqrtCalculus.inverseSqrt μ.xi2 r - β * xHat ζ r

/-- Strict convexity of the covariance inverse square root and actual
concavity of xHat imply strict convexity of the comparator. -/
theorem comparator_strictConvexOn (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {q : ℝ} (hq : HasCutoff ζ q)
    (hξ : StrictConvexOn ℝ (Ioo 0 1) (InverseSqrtCalculus.inverseSqrt μ.xi2)) :
    StrictConvexOn ℝ (Ioo 0 1) (comparator μ β ζ) := by
  have hhat : ConcaveOn ℝ (Ioo 0 1) (xHat ζ) :=
    (xHat_concave ζ hq).subset (subset_univ _) (convex_Ioo 0 1)
  exact hξ.sub_concaveOn (ConcaveOn.smul hβ hhat)

/-- The ordinary contact potential is the negative of the actual first
variation, with no separately supplied contact function. -/
noncomputable def potential (μ : FiniteMixture) (β : ℝ) (ζ : Measure ℝ) (r : ℝ) : ℝ :=
  -firstVariation β μ.xi ζ r

private theorem xi1_zero (μ : FiniteMixture) : μ.xi1 0 = 0 := by
  unfold FiniteMixture.xi1
  apply Finset.sum_eq_zero
  intro p hp
  have hp2 := μ.degree_ge_two hp
  rw [zero_pow (show p - 1 ≠ 0 by omega), mul_zero]

/-- The contact potential is differentiable at every point below one. -/
theorem potential_hasDerivAt (μ : FiniteMixture) (β : ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {q r : ℝ} (hq : HasCutoff ζ q) (hr : r < 1) :
    HasDerivAt (potential μ β ζ)
      (-(β ^ 2 * μ.xi1 r - ∫ t in (0 : ℝ)..r, 1 / (xHat ζ t) ^ 2)) r :=
  (firstVariation_hasDerivAt β μ.xi ζ hq hr (μ.hasDerivAt_xi r)).neg

/-- Twice differentiability and the actual second derivative of the contact
potential, obtained from the proved spatial first-variation calculus. -/
theorem potential_deriv_hasDerivAt (μ : FiniteMixture) (β : ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {q r : ℝ} (hq : HasCutoff ζ q) (hr : r < 1) :
    HasDerivAt (deriv (potential μ β ζ))
      (1 / (xHat ζ r) ^ 2 - β ^ 2 * μ.xi2 r) r := by
  have heq : deriv (potential μ β ζ) =
      (fun r => -deriv (firstVariation β μ.xi ζ) r) := by
    ext r
    exact deriv.neg
  rw [heq]
  convert (firstVariation_deriv_hasDerivAt β μ.xi ζ hq hr
    (differentiableOn_xi μ) (hasDerivAt_deriv_xi μ r)).neg using 1
  ring

/-- The actual contact potential and its first derivative vanish at the origin. -/
theorem potential_origin (μ : FiniteMixture) (β : ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {q : ℝ} (hq : HasCutoff ζ q) :
    potential μ β ζ 0 = 0 ∧ deriv (potential μ β ζ) 0 = 0 := by
  constructor
  · simp [potential, firstVariation, μ.xi_zero]
  · rw [(potential_hasDerivAt μ β ζ hq (by norm_num : (0 : ℝ) < 1)).deriv]
    simp [xi1_zero]

private theorem curvature_zero_iff_inverse_sqrt_comparator_zero
    {β v h : ℝ} (hβ : 0 < β) (hv : 0 < v) (hh : 0 < h) :
    1 / h ^ 2 - β ^ 2 * v = 0 ↔ (Real.sqrt v)⁻¹ - β * h = 0 := by
  have hspos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsne : Real.sqrt v ≠ 0 := hspos.ne'
  have hhne : h ≠ 0 := hh.ne'
  have hsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  have hprodpos : 0 < β * Real.sqrt v * h := mul_pos (mul_pos hβ hspos) hh
  constructor
  · intro hzero
    have hvalue : 1 / h ^ 2 = β ^ 2 * v := sub_eq_zero.mp hzero
    have hprodsq : (β * Real.sqrt v * h) ^ 2 = 1 := by
      calc
        _ = β ^ 2 * (Real.sqrt v) ^ 2 * h ^ 2 := by ring
        _ = β ^ 2 * v * h ^ 2 := by rw [hsq]
        _ = (1 / h ^ 2) * h ^ 2 := by rw [← hvalue]
        _ = 1 := by field_simp
    have hprod : β * Real.sqrt v * h = 1 := by nlinarith
    field_simp [hsne]
    nlinarith
  · intro hzero
    have hprod : β * Real.sqrt v * h = 1 := by
      field_simp [hsne] at hzero
      nlinarith
    have hnum : β ^ 2 * v * h ^ 2 = 1 := by
      calc
        _ = β ^ 2 * (Real.sqrt v) ^ 2 * h ^ 2 :=
          congrArg (fun w => β ^ 2 * w * h ^ 2) hsq.symm
        _ = (β * Real.sqrt v * h) ^ 2 := by ring
        _ = 1 := by rw [hprod]; norm_num
    field_simp [hhne]
    nlinarith

/-- Actual zero equivalence between the ordinary second derivative of the
contact potential and the concrete comparator. -/
theorem potential_deriv2_zero_iff_comparator_zero (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 < β) (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {q r : ℝ}
    (hq : HasCutoff ζ q) (hr : r ∈ Ioo 0 1) :
    deriv (deriv (potential μ β ζ)) r = 0 ↔ comparator μ β ζ r = 0 := by
  rw [(potential_deriv_hasDerivAt μ β ζ hq hr.2).deriv]
  unfold comparator InverseSqrtCalculus.inverseSqrt
  exact curvature_zero_iff_inverse_sqrt_comparator_zero hβ (μ.xi2_pos hr.1)
    (xHat_pos ζ hq hr.2)

/-- The actual minimizer contact potential is nonnegative on `[0,1)`, a
consequence of necessary optimality and the derived origin support point. -/
theorem potential_nonneg_of_minimizer (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) :
    ∀ r ∈ Ico 0 1, 0 ≤ potential μ β ζ.law r := by
  intro r hr
  exact neg_nonneg.mpr ((minimizer_firstVariation_maximum_zero μ hd hβ ζ hmin).1 r hr)

private theorem comparator_strictConvex_of_actual_covariance (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) (ζ : Admissible)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    StrictConvexOn ℝ (Ioo 0 1) (comparator μ β ζ.law) := by
  rw [μ.deriv_deriv_xi] at hξ
  have hξ' := hξ.subset (show Ioo (0 : ℝ) 1 ⊆ Ioc 0 1 from
    fun r hr => ⟨hr.1, hr.2.le⟩) (convex_Ioo 0 1)
  exact comparator_strictConvexOn μ hβ ζ.law ζ.hasCutoff hξ'

/-- Every actual minimizer under the inverse-curvature convexity hypothesis
has at most two actual contact points. Neither origin membership nor contact
count is assumed. -/
theorem minimizer_contacts_encard_le_two (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    {r | r ∈ Ico 0 1 ∧ potential μ β ζ.law r = 0}.encard ≤ 2 := by
  have h0 := potential_origin μ β ζ.law ζ.hasCutoff
  exact ContactGeometry.contacts_encard_le_two
    (fun r hr => (potential_hasDerivAt μ β ζ.law ζ.hasCutoff hr.2).differentiableAt)
    (fun r hr => (potential_deriv_hasDerivAt μ β ζ.law ζ.hasCutoff hr.2).differentiableAt)
    (potential_nonneg_of_minimizer μ hd hβ ζ hmin) h0.1 h0.2
    (comparator_strictConvex_of_actual_covariance μ hβ.le ζ hξ)
    (fun r hr => potential_deriv2_zero_iff_comparator_zero μ hβ ζ.law ζ.hasCutoff hr)

/-- A positive contact of an actual minimizer is necessarily nondegenerate,
with positive ordinary second derivative of its actual potential. -/
theorem minimizer_positive_contact_deriv2_pos (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    {Q : ℝ} (hQ : Q ∈ Ioo 0 1) (hVQ : potential μ β ζ.law Q = 0) :
    0 < deriv (deriv (potential μ β ζ.law)) Q := by
  have h0 := potential_origin μ β ζ.law ζ.hasCutoff
  exact ContactGeometry.positive_contact_deriv2_pos
    (fun r hr => (potential_hasDerivAt μ β ζ.law ζ.hasCutoff hr.2).differentiableAt)
    (fun r hr => (potential_deriv_hasDerivAt μ β ζ.law ζ.hasCutoff hr.2).differentiableAt)
    (potential_nonneg_of_minimizer μ hd hβ ζ hmin) h0.1 h0.2
    (comparator_strictConvex_of_actual_covariance μ hβ.le ζ hξ)
    (fun r hr => potential_deriv2_zero_iff_comparator_zero μ hβ ζ.law ζ.hasCutoff hr) hQ hVQ

/-- The actual topological support of a minimizer is contained in its actual
potential contact set. -/
theorem minimizer_support_subset_contacts (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) :
    ζ.law.support ⊆ {r | r ∈ Ico 0 1 ∧ potential μ β ζ.law r = 0} := by
  intro r hr
  have hb := support_subset_cutoff ζ.law ζ.hasCutoff hr
  exact ⟨⟨hb.1, hb.2.trans_lt ζ.hasCutoff.2.1⟩,
    by unfold potential; rw [(minimizer_firstVariation_maximum_zero μ hd hβ ζ hmin).2.2 r hr]; simp⟩

/-- Actual minimizer support has at most two points under the covariance
inverse-square-root convexity hypothesis. -/
theorem minimizer_support_encard_le_two (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    ζ.law.support.encard ≤ 2 :=
  (Set.encard_mono (minimizer_support_subset_contacts μ hd hβ ζ hmin)).trans
    (minimizer_contacts_encard_le_two μ hd hβ ζ hmin hξ)

/-- A probability law concentrated almost everywhere at zero is the actual
Dirac probability law, derived from its finite-support measure decomposition. -/
theorem eq_diracZero_of_ae_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hae : ∀ᵐ r ∂ν, r = 0) : ν = Measure.dirac (0 : ℝ) := by
  have hfinite : ∀ᵐ r ∂ν, r ∈ ({0} : Finset ℝ) := by simpa using hae
  have hrepr := (Measure.ae_mem_finset_iff (s := ({0} : Finset ℝ))).mp hfinite
  simp only [Finset.sum_singleton] at hrepr
  have hmass : ν {0} = 1 := by
    have h := congrArg (fun σ : Measure ℝ => σ univ) hrepr
    simpa only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one] using h.symm
  rw [hmass] at hrepr
  simpa using hrepr

/-- Above the static threshold an actual minimizer cannot be the zero atom,
by the proved replica-symmetric minimizer classification. -/
theorem minimizer_ne_diracZero_of_gt_staticThreshold (μ : FiniteMixture)
    {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β)
    (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) : ζ.law ≠ Measure.dirac (0 : ℝ) := by
  intro heq
  have hβ : 0 ≤ β := (lt_trans μ.staticThreshold_pos hgt).le
  have hdirac : CSReplicaSymmetric.DiracZeroMinimal μ β := by
    intro ν hν q hq
    let νA : Admissible := ⟨ν, hν, ⟨q, hq⟩⟩
    have h := hmin νA
    rw [ζ.value_eq β μ.xi ζ.hasCutoff, νA.value_eq β μ.xi hq, heq,
      CSReplicaSymmetric.functional_diracZero_at_cutoff μ β ζ.hasCutoff.1 ζ.hasCutoff.2.1] at h
    rw [CSReplicaSymmetric.functional_diracZero μ β]
    exact h
  exact (not_le_of_gt hgt)
    ((CSReplicaSymmetric.diracZeroMinimal_iff_le_staticThreshold μ hβ).mp hdirac)

/-- Every nonzero-atom admissible law has a genuinely positive support point. -/
theorem exists_positive_support_of_ne_diracZero (ζ : Admissible)
    (hne : ζ.law ≠ Measure.dirac (0 : ℝ)) :
    ∃ Q ∈ ζ.law.support, Q ∈ Ioo 0 1 := by
  by_contra hnot
  have hsupp : ∀ᵐ r ∂ζ.law, r ∈ ζ.law.support := ζ.law.support_mem_ae
  have hae0 : ∀ᵐ r ∂ζ.law, r = 0 := by
    filter_upwards [hsupp] with r hr
    have hb := support_subset_cutoff ζ.law ζ.hasCutoff hr
    by_contra hr0
    have hrpos : 0 < r := lt_of_le_of_ne hb.1 (Ne.symm hr0)
    exact hnot ⟨r, hr, ⟨hrpos, hb.2.trans_lt ζ.hasCutoff.2.1⟩⟩
  exact hne (eq_diracZero_of_ae_zero ζ.law hae0)

/-- Above the static threshold, the support and contact set of any actual
minimizer under strict inverse-curvature convexity consist exactly of `{0,Q}`,
with an actual positive nondegenerate contact `Q`. -/
theorem minimizer_two_contacts_of_gt_staticThreshold (μ : FiniteMixture)
    (hd : 3 ≤ μ.minDegree) {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β)
    (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    ∃ Q ∈ Ioo 0 1, ζ.law.support = {0, Q} ∧
      {r | r ∈ Ico 0 1 ∧ potential μ β ζ.law r = 0} = {0, Q} ∧
      deriv (potential μ β ζ.law) Q = 0 ∧
      0 < deriv (deriv (potential μ β ζ.law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q → 0 < potential μ β ζ.law r := by
  have hβ : 0 < β := lt_trans μ.staticThreshold_pos hgt
  obtain ⟨Q, hQs, hQ⟩ := exists_positive_support_of_ne_diracZero ζ
    (minimizer_ne_diracZero_of_gt_staticThreshold μ hgt ζ hmin)
  have hVQ : potential μ β ζ.law Q = 0 :=
    (minimizer_support_subset_contacts μ hd hβ ζ hmin hQs).2
  have h0 := potential_origin μ β ζ.law ζ.hasCutoff
  have hVdiff := fun r (hr : r ∈ Ico (0 : ℝ) 1) =>
    (potential_hasDerivAt μ β ζ.law ζ.hasCutoff hr.2).differentiableAt
  have hVdiff' := fun r (hr : r ∈ Ico (0 : ℝ) 1) =>
    (potential_deriv_hasDerivAt μ β ζ.law ζ.hasCutoff hr.2).differentiableAt
  have hVnonneg := potential_nonneg_of_minimizer μ hd hβ ζ hmin
  have hD := comparator_strictConvex_of_actual_covariance μ hβ.le ζ hξ
  have hzero := fun r (hr : r ∈ Ioo (0 : ℝ) 1) =>
    potential_deriv2_zero_iff_comparator_zero μ hβ ζ.law ζ.hasCutoff hr
  have hcontacts := ContactGeometry.contacts_eq_zero_and_positive
    hVdiff hVdiff' hVnonneg h0.1 h0.2 hD hzero hQ hVQ
  have hsupport : ζ.law.support = {0, Q} := by
    apply Set.Subset.antisymm
    · rw [← hcontacts]
      exact minimizer_support_subset_contacts μ hd hβ ζ hmin
    · intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact origin_mem_support_of_minimizer μ hd hβ ζ hmin
      · exact hQs
  exact ⟨Q, hQ, hsupport, hcontacts,
    ContactGeometry.contact_deriv_zero hVnonneg hQ hVQ,
    minimizer_positive_contact_deriv2_pos μ hd hβ ζ hmin hξ hQ hVQ,
    fun r hr hrQ => ContactGeometry.potential_pos_away_from_positive_contact
      hVdiff hVdiff' hVnonneg h0.1 h0.2 hD hzero hQ hVQ hr hrQ⟩

/-- A genuine probability law with exactly two support points `0<Q` has the
literal one-step form with a strictly interior real atom weight. -/
theorem twoAtom_of_support_pair (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {Q : ℝ} (hQ : 0 < Q) (hsupport : ν.support = {0, Q}) :
    ∃ x ∈ Ioo 0 1, ν = twoAtom x Q := by
  have hsupp : ∀ᵐ r ∂ν, r ∈ ν.support := ν.support_mem_ae
  have hae : ∀ᵐ r ∂ν, r = 0 ∨ r = Q := by simpa [hsupport] using hsupp
  have hrepr := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hQ.ne).mp hae
  have h0supp : (0 : ℝ) ∈ ν.support := by rw [hsupport]; simp
  have hQsupp : Q ∈ ν.support := by rw [hsupport]; simp
  have h0pos : 0 < ν {0} := by
    have h := (Measure.mem_support_iff_forall 0).mp h0supp (Iio Q) (Iio_mem_nhds hQ)
    rw [hrepr] at h
    simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hQ] using h
  have hQpos : 0 < ν {Q} := by
    have h := (Measure.mem_support_iff_forall Q).mp hQsupp (Ioi 0) (Ioi_mem_nhds hQ)
    rw [hrepr] at h
    simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hQ] using h
  have hsum : ν {0} + ν {Q} = 1 := by
    have h := congrArg (fun σ : Measure ℝ => σ univ) hrepr
    simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul] using h.symm
  have h0top := measure_ne_top ν {0}
  have hQtop := measure_ne_top ν {Q}
  have hsumReal : (ν {0}).toReal + (ν {Q}).toReal = 1 := by
    have h := congrArg ENNReal.toReal hsum
    simpa [ENNReal.toReal_add h0top hQtop] using h
  have hxpos : 0 < (ν {0}).toReal := ENNReal.toReal_pos h0pos.ne' h0top
  have hotherpos : 0 < (ν {Q}).toReal := ENNReal.toReal_pos hQpos.ne' hQtop
  have hxlt : (ν {0}).toReal < 1 := by linarith
  refine ⟨(ν {0}).toReal, ⟨hxpos, hxlt⟩, ?_⟩
  have hremaining : 1 - (ν {0}).toReal = (ν {Q}).toReal := by linarith
  unfold twoAtom
  rw [ENNReal.ofReal_toReal h0top, hremaining, ENNReal.ofReal_toReal hQtop]
  exact hrepr

/-- The actual one-step conclusion for every genuine above-threshold
minimizer under strict inverse-curvature convexity, with both atom weights
strictly positive and the positive contact nondegenerate. -/
theorem minimizer_strict_oneStep_of_gt_staticThreshold (μ : FiniteMixture)
    (hd : 3 ≤ μ.minDegree) {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β)
    (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    ∃ x ∈ Ioo 0 1, ∃ Q ∈ Ioo 0 1,
      ζ.law = twoAtom x Q ∧ potential μ β ζ.law Q = 0 ∧
      deriv (potential μ β ζ.law) Q = 0 ∧
      0 < deriv (deriv (potential μ β ζ.law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q → 0 < potential μ β ζ.law r := by
  obtain ⟨Q, hQ, hsupport, hcontacts, hderiv, hcurv, hpositive⟩ :=
    minimizer_two_contacts_of_gt_staticThreshold μ hd hgt ζ hmin hξ
  obtain ⟨x, hx, hlaw⟩ := twoAtom_of_support_pair ζ.law hQ.1 hsupport
  have hVQ : potential μ β ζ.law Q = 0 := by
    have hmem : Q ∈ {r | r ∈ Ico 0 1 ∧ potential μ β ζ.law r = 0} := by
      rw [hcontacts]
      simp
    exact hmem.2
  exact ⟨x, hx, Q, hQ, hlaw, hVQ, hderiv, hcurv, hpositive⟩

/-- The degree-window criterion gives the actual strict one-step structure
of every above-threshold minimizer, combining the coefficient/moment curvature
proof with the genuine variational contact geometry. -/
theorem degree_window_minimizer_strict_oneStep (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β)
    (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) :
    ∃ x ∈ Ioo 0 1, ∃ Q ∈ Ioo 0 1,
      ζ.law = twoAtom x Q ∧ potential μ β ζ.law Q = 0 ∧
      deriv (potential μ β ζ.law) Q = 0 ∧
      0 < deriv (deriv (potential μ β ζ.law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q → 0 < potential μ β ζ.law r :=
  minimizer_strict_oneStep_of_gt_staticThreshold μ (by omega) hgt ζ hmin
    (μ.degree_window_strictConvexOn hwindow)

end SlowEquilibration.CSStructure
