-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSFirstVariation
public import SlowEquilibration.CSLawInjective
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology

private lemma integrable_on_cutoff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : HasCutoff μ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 q)) : Integrable f μ := by
  have hi := hf.integrableOn_compact isCompact_Icc (μ := μ)
  simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hq.2.2] using hi

/-- Convexity of the reciprocal on positive numbers, proved from its
supporting inequality. -/
theorem reciprocal_convex_combination {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hx : 0 < x) (hy : 0 < y) :
    (a*x+b*y)⁻¹ ≤ a*x⁻¹+b*y⁻¹ := by
  let z := a*x+b*y
  have hz : 0 < z := by
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      simp [z, ha0, hb1, hy]
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx)
        (mul_nonneg hb hy.le)
  have h1 := reciprocal_supporting_inequality hz hx
  have h2 := reciprocal_supporting_inequality hz hy
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  have hcancel : a*(-(x-z)/z^2)+b*(-(y-z)/z^2)=0 := by
    calc
      a*(-(x-z)/z^2)+b*(-(y-z)/z^2) = (-(a*x+b*y)+(a+b)*z)*(z^2)⁻¹ := by
        simp only [div_eq_mul_inv]
        ring
      _ = 0 := by rw [hab]; dsimp only [z]; ring
  rw [hcancel] at h
  have hright : a*(x⁻¹-z⁻¹)+b*(y⁻¹-z⁻¹)=a*x⁻¹+b*y⁻¹-z⁻¹ := by
    calc
      _ = a*x⁻¹+b*y⁻¹-(a+b)*z⁻¹ := by ring
      _ = _ := by rw [hab, one_mul]
  rw [hright] at h
  linarith

/-- The actual Crisanti--Sommers functional is convex along every affine
segment of admissible probability laws with a common support cutoff. -/
theorem functional_mixture_convex (β : ℝ) (η : ℝ → ℝ)
    (ζ μ : Measure ℝ) [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q)
    (hη : ContinuousOn η (Icc 0 q)) :
    ConvexOn ℝ (Icc 0 1) (fun t => functional β η (mixture ζ μ t) q) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro u hu v hv a b ha hb hab
  have hw : a*u+b*v ∈ Icc (0:ℝ) 1 := (convex_Icc (0:ℝ) 1) hu hv ha hb hab
  have hprobU : IsProbabilityMeasure (mixture ζ μ u) := mixture_isProbability ζ μ hu
  have hprobV : IsProbabilityMeasure (mixture ζ μ v) := mixture_isProbability ζ μ hv
  have hprobW : IsProbabilityMeasure (mixture ζ μ (a*u+b*v)) := mixture_isProbability ζ μ hw
  have hcutU := mixture_cutoff ζ μ hζ hμ (t := u)
  have hcutV := mixture_cutoff ζ μ hζ hμ (t := v)
  have hcutW := mixture_cutoff ζ μ hζ hμ (t := a*u+b*v)
  have hJU := inverse_xHat_intervalIntegrable (mixture ζ μ u) hcutU
    (a := 0) (b := q) (by norm_num) hζ.2.1
  have hJV := inverse_xHat_intervalIntegrable (mixture ζ μ v) hcutV
    (a := 0) (b := q) (by norm_num) hζ.2.1
  have hJW := inverse_xHat_intervalIntegrable (mixture ζ μ (a*u+b*v)) hcutW
    (a := 0) (b := q) (by norm_num) hζ.2.1
  have hJpoint : ∀ s ∈ Icc 0 q,
      (xHat (mixture ζ μ (a*u+b*v)) s)⁻¹ ≤
        a*(xHat (mixture ζ μ u) s)⁻¹+b*(xHat (mixture ζ μ v) s)⁻¹ := by
    intro s hs
    have hmix : xHat (mixture ζ μ (a*u+b*v)) s =
        a*xHat (mixture ζ μ u) s+b*xHat (mixture ζ μ v) s := by
      rw [xHat_mixture ζ μ hζ hμ hw, xHat_mixture ζ μ hζ hμ hu,
        xHat_mixture ζ μ hζ hμ hv]
      linear_combination -(xHat ζ s)*hab
    rw [hmix]
    exact reciprocal_convex_combination ha hb hab
      (xHat_pos (mixture ζ μ u) hcutU (hs.2.trans_lt hζ.2.1))
      (xHat_pos (mixture ζ μ v) hcutV (hs.2.trans_lt hζ.2.1))
  have hJ := intervalIntegral.integral_mono_on hζ.1 hJW
    ((hJU.const_mul a).add (hJV.const_mul b)) hJpoint
  have hJsum : (∫ s in (0:ℝ)..q, a*(xHat (mixture ζ μ u) s)⁻¹+
      b*(xHat (mixture ζ μ v) s)⁻¹) =
      a*(∫ s in (0:ℝ)..q, (xHat (mixture ζ μ u) s)⁻¹)+
        b*(∫ s in (0:ℝ)..q, (xHat (mixture ζ μ v) s)⁻¹) := by
    rw [intervalIntegral.integral_add (hJU.const_mul a) (hJV.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hJsum] at hJ
  have hiζ := integrable_on_cutoff ζ hζ hη
  have hiμ := integrable_on_cutoff μ hμ hη
  have hI : (∫ s, η s ∂mixture ζ μ (a*u+b*v)) =
      a*(∫ s, η s ∂mixture ζ μ u)+b*(∫ s, η s ∂mixture ζ μ v) := by
    rw [integral_mixture ζ μ hiζ hiμ hw, integral_mixture ζ μ hiζ hiμ hu,
      integral_mixture ζ μ hiζ hiμ hv]
    linear_combination -(∫ s, η s ∂ζ)*hab
  have hconst : a*(β^2*η 1+Real.log (1-q))+b*(β^2*η 1+Real.log (1-q)) =
      β^2*η 1+Real.log (1-q) := by rw [← add_mul, hab, one_mul]
  change functional β η (mixture ζ μ (a*u+b*v)) q ≤
    a*functional β η (mixture ζ μ u) q+b*functional β η (mixture ζ μ v) q
  unfold functional
  rw [hI]
  nlinarith

/-- Strict reciprocal convexity at the midpoint of distinct positive values. -/
theorem reciprocal_midpoint_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    ((x+y)/2)⁻¹ < (x⁻¹+y⁻¹)/2 := by
  have hsum := add_pos hx hy
  have hleft : ((x+y)/2)⁻¹=2/(x+y) := by field_simp
  have hright : (x⁻¹+y⁻¹)/2=(x+y)/(2*x*y) := by field_simp; ring
  rw [hleft, hright]
  apply (div_lt_div_iff₀ hsum (by positivity)).mpr
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

private lemma reciprocal_midpoint_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((x+y)/2)⁻¹ ≤ (x⁻¹+y⁻¹)/2 := by
  have h := reciprocal_convex_combination (a := (1:ℝ)/2) (b := (1:ℝ)/2)
    (by norm_num) (by norm_num) (by norm_num) hx hy
  have hblend : (1:ℝ)/2*x+(1:ℝ)/2*y=(x+y)/2 := by ring
  rw [hblend] at h
  convert h using 1
  ring

/-- Distinct admissible probability laws have distinct hatted functions
somewhere on their common support cutoff. -/
theorem exists_xHat_ne_on_cutoff (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q) (hne : ζ ≠ μ) :
    ∃ s ∈ Icc 0 q, xHat ζ s ≠ xHat μ s := by
  by_contra h
  push Not at h
  exact hne (measure_eq_of_xHat_eq_on_cutoff ζ μ hζ hμ h)

private lemma inverse_xHat_continuousOn (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : ContinuousOn (fun s => (xHat ζ s)⁻¹) (Icc 0 q) := by
  apply (xHat_continuous ζ hq).continuousOn.inv₀
  intro s hs
  exact (xHat_pos ζ hq (hs.2.trans_lt hq.2.1)).ne'

/-- The entropy integral is strictly convex between distinct genuine laws,
using the proved injectivity of xHat and strictness on an actual interval. -/
theorem inverse_xHat_midpoint_integral_strict (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q) (hne : ζ ≠ μ) :
    (∫ s in (0:ℝ)..q, (xHat (mixture ζ μ (1/2)) s)⁻¹) <
      ((∫ s in (0:ℝ)..q, (xHat ζ s)⁻¹)+(∫ s in (0:ℝ)..q, (xHat μ s)⁻¹))/2 := by
  have ht : (1:ℝ)/2 ∈ Icc 0 1 := by norm_num
  have hprob : IsProbabilityMeasure (mixture ζ μ (1/2)) := mixture_isProbability ζ μ ht
  have hcut := mixture_cutoff ζ μ hζ hμ (t := (1:ℝ)/2)
  have hhalf : ∀ s, xHat (mixture ζ μ (1/2)) s=(xHat ζ s+xHat μ s)/2 := by
    intro s
    rw [xHat_mixture ζ μ hζ hμ ht]
    ring
  obtain ⟨s, hs, hneHat⟩ := exists_xHat_ne_on_cutoff ζ μ hζ hμ hne
  have hsq : s < q := lt_of_le_of_ne hs.2 (by
    intro heq
    apply hneHat
    rw [heq, xHat_tail ζ hζ le_rfl, xHat_tail μ hμ le_rfl])
  have hq : 0 < q := hs.1.trans_lt hsq
  have hJ := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hq
    (inverse_xHat_continuousOn (mixture ζ μ (1/2)) hcut)
    (((inverse_xHat_continuousOn ζ hζ).add (inverse_xHat_continuousOn μ hμ)).div_const 2)
    (fun r hr => by
      rw [hhalf]
      exact reciprocal_midpoint_le (xHat_pos ζ hζ (hr.2.trans_lt hζ.2.1))
        (xHat_pos μ hμ (hr.2.trans_lt hμ.2.1)))
    ⟨s, hs, by
      rw [hhalf]
      exact reciprocal_midpoint_strict (xHat_pos ζ hζ (hs.2.trans_lt hζ.2.1))
        (xHat_pos μ hμ (hs.2.trans_lt hμ.2.1)) hneHat⟩
  have hiζ := inverse_xHat_intervalIntegrable ζ hζ (a := 0) (b := q) (by norm_num) hζ.2.1
  have hiμ := inverse_xHat_intervalIntegrable μ hμ (a := 0) (b := q) (by norm_num) hμ.2.1
  have hright : (∫ s in (0:ℝ)..q, ((xHat ζ s)⁻¹+(xHat μ s)⁻¹)/2) =
      ((∫ s in (0:ℝ)..q, (xHat ζ s)⁻¹)+(∫ s in (0:ℝ)..q, (xHat μ s)⁻¹))/2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hiζ hiμ]
  change (∫ s in (0:ℝ)..q, (xHat (mixture ζ μ (1/2)) s)⁻¹) <
    (∫ s in (0:ℝ)..q, ((xHat ζ s)⁻¹+(xHat μ s)⁻¹)/2) at hJ
  rwa [hright] at hJ

/-- Strict midpoint convexity of the actual functional for distinct laws. -/
theorem functional_midpoint_strict (β : ℝ) (η : ℝ → ℝ)
    (ζ μ : Measure ℝ) [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q)
    (hη : ContinuousOn η (Icc 0 q)) (hne : ζ ≠ μ) :
    functional β η (mixture ζ μ (1/2)) q <
      (functional β η ζ q+functional β η μ q)/2 := by
  have hJ := inverse_xHat_midpoint_integral_strict ζ μ hζ hμ hne
  have hI := integral_mixture ζ μ (integrable_on_cutoff ζ hζ hη)
    (integrable_on_cutoff μ hμ hη) (t := (1:ℝ)/2) (by norm_num)
  unfold functional
  rw [hI]
  nlinarith

/-- Uniqueness of a Crisanti--Sommers minimizer among the actual admissible
probability measures; no uniqueness axiom or distribution surrogate is used. -/
theorem Admissible.minimizer_law_unique (ζ μ : Admissible)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1))
    (hζmin : ζ.IsMinimizer β η) (hμmin : μ.IsMinimizer β η) : ζ.law = μ.law := by
  by_contra hne
  let q := max ζ.cutoff μ.cutoff
  have hq1 : q < 1 := max_lt ζ.hasCutoff.2.1 μ.hasCutoff.2.1
  have hζq : HasCutoff ζ.law q := ζ.hasCutoff.mono (le_max_left _ _) hq1
  have hμq : HasCutoff μ.law q := μ.hasCutoff.mono (le_max_right _ _) hq1
  have hηq : ContinuousOn η (Icc 0 q) :=
    hη.mono (fun r hr => ⟨hr.1, hr.2.trans_lt hq1⟩)
  let ν : Admissible := ⟨mixture ζ.law μ.law (1/2),
    mixture_isProbability ζ.law μ.law (by norm_num),
    ⟨q, mixture_cutoff ζ.law μ.law hζq hμq⟩⟩
  have hstrict := functional_midpoint_strict β η ζ.law μ.law hζq hμq hηq hne
  change functional β η ν.law q < (functional β η ζ.law q+functional β η μ.law q)/2 at hstrict
  rw [← ν.value_eq β η (mixture_cutoff ζ.law μ.law hζq hμq),
    ← ζ.value_eq β η hζq, ← μ.value_eq β η hμq] at hstrict
  have hminν := hζmin ν
  have hminμ := hζmin μ
  have hminζ := hμmin ζ
  linarith

/-- The canonical admissible object is also unique, since its remaining
fields are proofs of probability and admissibility. -/
theorem Admissible.minimizer_unique (ζ μ : Admissible)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1))
    (hζmin : ζ.IsMinimizer β η) (hμmin : μ.IsMinimizer β η) : ζ = μ := by
  have h := ζ.minimizer_law_unique μ β η hη hζmin hμmin
  cases ζ
  cases μ
  cases h
  rfl

end SlowEquilibration.CrisantiSommers
