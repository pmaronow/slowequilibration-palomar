-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceInitialQuantitativeInput
public import SlowEquilibration.SphericalMenuReduction

/-! Manuscript `thm:main-initial` (ii): polynomial menus of prescribed
sphere-supported initial laws remain separated from Gibbs, simultaneously
over all convex weights and all times up to the common source horizon.
The quantitative CP input gives an entry exponent strictly above the menu
growth exponent. The same bound applies to an independent random menu
under the product law of menu randomness and the complete field. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceInitialPolynomialMenu

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalFieldKernels SphericalMenuReduction
open SourceInitialQuantitativeInput SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal

set_option autoImplicit false

/-- Source `thm:main-initial` (ii): choose a fixed Holder order whose CP
decay exponent exceeds the polynomial menu growth exponent. -/
theorem polynomial_menu_size_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (B : ∀ N, ℝ → Set (Field N μ × Vector N))
    (S : QuantitativeUniformStart μ β T B)
    {ι : ℕ → Type*} [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
    {κ C₀ : ℝ} (hκ : 0 ≤ κ) (hκα : κ < alpha μ)
    (hC₀ : 0 < C₀)
    (hcard : ∀ᶠ N in atTop,
      (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) :
    ∀ M : ℝ, 0 < M →
      Tendsto
        (fun N => (Fintype.card (ι N) : ℝ) *
          SphericalFieldKernels.uniformEntryMass μ β (T N) (B N M))
        atTop (𝓝 0) := by
  have hα : 0 < alpha μ := lt_of_le_of_lt hκ hκα
  have hδ : 0 < alpha μ - κ := sub_pos.mpr hκα
  let r : ℝ := 2 * alpha μ / (alpha μ - κ)
  have hr : 1 < r := by
    dsimp [r]
    apply (lt_div_iff₀ hδ).2
    linarith
  have hrpos : 0 < r := by linarith
  have hmul : (alpha μ - κ) * r = 2 * alpha μ := by
    dsimp [r]
    field_simp
  have hdiv : alpha μ / r < alpha μ - κ := by
    apply (div_lt_iff₀ hrpos).2
    rw [hmul]
    linarith
  have hgap : 0 < alpha μ * (1 - 1/r) - κ := by
    have he : alpha μ * (1 - 1/r) = alpha μ - alpha μ / r := by ring
    rw [he]
    linarith
  intro M hM
  obtain ⟨C, hC, hrate⟩ := S.rate M r hM hr
  have hq (N : ℕ) : 0 ≤ uniformEntryMass μ β (T N) (B N M) := by
    unfold uniformEntryMass SphericalRotationCovariance.uniformExpectedEventMass
    exact integral_nonneg fun _ => measureReal_nonneg
  have hbound : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (ι N) : ℝ) * uniformEntryMass μ β (T N) (B N M) ≤
        (C₀ * C) * (N : ℝ)^(-(alpha μ * (1 - 1/r) - κ)) := by
    filter_upwards [hcard, hrate, eventually_ge_atTop (1 : ℕ)] with N hcardN hrateN hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    calc
      (Fintype.card (ι N) : ℝ) * uniformEntryMass μ β (T N) (B N M)
          ≤ (C₀ * (N : ℝ)^κ) * (C * (N : ℝ)^(-alpha μ * (1 - 1/r))) :=
        mul_le_mul hcardN hrateN (hq N)
          (mul_nonneg hC₀.le (Real.rpow_nonneg hNpos.le _))
      _ = (C₀ * C) * (N : ℝ)^(-(alpha μ * (1 - 1/r) - κ)) := by
        rw [show -(alpha μ * (1 - 1/r) - κ) = κ + -alpha μ * (1 - 1/r) by ring,
          Real.rpow_add hNpos]
        ring
  have hpow : Tendsto
      (fun N : ℕ => (C₀ * C) * (N : ℝ)^(-(alpha μ * (1 - 1/r) - κ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop hgap).comp tendsto_natCast_atTop_atTop).const_mul (C₀ * C)
  exact squeeze_zero' (.of_forall fun N => mul_nonneg (Nat.cast_nonneg _) (hq N))
    hbound hpow

/-- Source `thm:main-initial` (ii) for prescribed menus: the literal
joint time/weight infimum tends to one, permitting field-dependent weights. -/
theorem polynomial_menu_allTime_separation
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (B : ∀ N, ℝ → Set (Field N μ × Vector N))
    (S : QuantitativeUniformStart μ β T B)
    {ι : ℕ → Type*} [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
    (ν : ∀ N, ι N → Measure (Vector N))
    [∀ N j, IsProbabilityMeasure (ν N j)]
    (hsupport : ∀ N, 2 ≤ N → ∀ j,
      ∀ᵐ x ∂ν N j, OnSphere x)
    {κ C₀ : ℝ} (hκ : 0 ≤ κ) (hκα : κ < alpha μ)
    (hC₀ : 0 < C₀)
    (hcard : ∀ᶠ N in atTop,
      (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) :
    VaryingProbability.InProbability
      (fun N => SphericalFieldKernels.fieldLaw N μ)
      (fun N =>
        SphericalMenuReduction.physicalMenuDistance μ β (ν N) (T N))
      1 := by
  exact prescribed_menu_allTime_separation μ β T ν B S.measurable hsupport
    S.rotation S.capture
    (polynomial_menu_size_tendsto_zero μ β T B S hκ hκα hC₀ hcard)

/-- Source `thm:main-initial` (ii), independent-random-menu clause:
the same simultaneous separation holds in the joint product probability. -/
theorem polynomial_random_menu_allTime_separation
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (B : ∀ N, ℝ → Set (Field N μ × Vector N))
    (S : QuantitativeUniformStart μ β T B)
    {ι : ℕ → Type*} [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
    {R : ℕ → Type*} [∀ N, MeasurableSpace (R N)]
    (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
    (ν : ∀ N, R N → ι N → Measure (Vector N))
    (hν : ∀ N j, Measurable (fun r => ν N r j))
    [∀ N r j, IsProbabilityMeasure (ν N r j)]
    (hsupport : ∀ N, 2 ≤ N → ∀ r j,
      ∀ᵐ x ∂ν N r j, OnSphere x)
    {κ C₀ : ℝ} (hκ : 0 ≤ κ) (hκα : κ < alpha μ)
    (hC₀ : 0 < C₀)
    (hcard : ∀ᶠ N in atTop,
      (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) :
    VaryingProbability.InProbability
      (fun N => (ρ N).prod (SphericalFieldKernels.fieldLaw N μ))
      (fun N z =>
        SphericalMenuReduction.physicalMenuDistance
          μ β (ν N z.1) (T N) z.2)
      1 := by
  exact independent_random_menu_allTime_separation μ β T ρ ν hν B S.measurable
    hsupport S.rotation S.capture
    (polynomial_menu_size_tendsto_zero μ β T B S hκ hκα hC₀ hcard)

end SlowEquilibration.SourceInitialPolynomialMenu
