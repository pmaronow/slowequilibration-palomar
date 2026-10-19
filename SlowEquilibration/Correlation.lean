-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Hilbert-space correlation and projection estimates

This file proves the Hilbert-space steps in manuscript Lemmas
`lem:sp-correlation` and `lem:sp-projection`. The space is arbitrary and
may be infinite dimensional; in the intended application it is the real
Hilbert space of vector-valued square-integrable observables.

The energy bounds on the semigroup displacement and on the projection
tail are explicit analytic inputs. This file does not construct the
spherical diffusion, its generator, the Dirichlet form, or its spectral
projections, and does not prove these energy bounds for that generator.
Centering is unnecessary for the Hilbert-space inequalities themselves.
-/

namespace SlowEquilibration

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The scalar inequality used to bound a symmetric diffusion-semigroup
displacement by its Dirichlet energy. -/
theorem one_sub_exp_neg_sq_le (x : ℝ) (hx : 0 ≤ x) :
    (1 - Real.exp (-x)) ^ 2 ≤ x := by
  have hnon : 0 ≤ 1 - Real.exp (-x) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  have hone : 1 - Real.exp (-x) ≤ 1 := by
    linarith [Real.exp_pos (-x)]
  have hxbound : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.add_one_le_exp (-x)]
  nlinarith

/-- Alignment with an observable of norm at most one forces a lower bound
on the image under a symmetric operator, up to its displacement error. -/
theorem norm_image_lower_of_displacement (S : H →L[ℝ] H)
    (hS : (S : H →ₗ[ℝ] H).IsSymmetric) (Z B : H) (ε : ℝ)
    (hZ : ‖Z‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hε : 0 ≤ ε)
    (herror : ‖B - S B‖ ≤ ε) :
    max 0 (⟪Z, B⟫_ℝ - ε) ≤ ‖S Z‖ := by
  have hsplit : ⟪Z, B⟫_ℝ =
      ⟪S Z, B⟫_ℝ + ⟪Z, B - S B⟫_ℝ := by
    rw [inner_sub_right, hS.apply_clm Z B]
    ring
  have hleft : ⟪S Z, B⟫_ℝ ≤ ‖S Z‖ :=
    (real_inner_le_norm _ _).trans
      (by nlinarith [norm_nonneg (S Z)])
  have hright : ⟪Z, B - S B⟫_ℝ ≤ ε := by
    calc
      _ ≤ ‖Z‖ * ‖B - S B‖ := real_inner_le_norm _ _
      _ ≤ ‖Z‖ * ε := mul_le_mul_of_nonneg_left herror (norm_nonneg Z)
      _ ≤ ε := by nlinarith
  exact max_le (norm_nonneg _) (by linarith)

/-- The positive-square correlation estimate for a symmetric operator
square. No finite-dimensional representation is used. -/
theorem correlation_lower_of_displacement (S : H →L[ℝ] H)
    (hS : (S : H →ₗ[ℝ] H).IsSymmetric) (Z B : H) (ε : ℝ)
    (hZ : ‖Z‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hε : 0 ≤ ε)
    (herror : ‖B - S B‖ ≤ ε) :
    (max 0 (⟪Z, B⟫_ℝ - ε)) ^ 2 ≤ ⟪Z, S (S Z)⟫_ℝ := by
  have hnorm := norm_image_lower_of_displacement S hS Z B ε hZ hB hε herror
  have hsq : (max 0 (⟪Z, B⟫_ℝ - ε)) ^ 2 ≤ ‖S Z‖ ^ 2 := by
    have hmax : 0 ≤ max 0 (⟪Z, B⟫_ℝ - ε) := le_max_left _ _
    nlinarith [norm_nonneg (S Z)]
  simpa only [← real_inner_self_eq_norm_sq, hS.apply_clm Z (S Z)] using hsq

/-- The direct correlation estimate of manuscript `lem:sp-correlation`,
from the symmetric semigroup square identity and the analytic energy
estimate `‖B - P(t/2) B‖² ≤ t E / 2`.

The energy estimate remains an explicit input; the conclusion is proved
from that input and the actual Hilbert-space operator identities. -/
theorem direct_correlation_estimate (P : ℝ → H →L[ℝ] H)
    (Z B : H) (t E : ℝ) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (hZ : ‖Z‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hsymmetric : (P (t / 2) : H →ₗ[ℝ] H).IsSymmetric)
    (hsquare : P t = (P (t / 2)).comp (P (t / 2)))
    (henergy : ‖B - P (t / 2) B‖ ^ 2 ≤ t * E / 2) :
    (max 0 (⟪Z, B⟫_ℝ - Real.sqrt (t * E / 2))) ^ 2 ≤
      ⟪Z, P t Z⟫_ℝ := by
  have hq : 0 ≤ t * E / 2 := by positivity
  have herror : ‖B - P (t / 2) B‖ ≤ Real.sqrt (t * E / 2) := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg (t * E / 2),
      norm_nonneg (B - P (t / 2) B)]
  simpa only [hsquare, ContinuousLinearMap.comp_apply] using
    correlation_lower_of_displacement (P (t / 2)) hsymmetric Z B
      (Real.sqrt (t * E / 2)) hZ hB (Real.sqrt_nonneg _) herror

/-- The alignment part of manuscript `lem:sp-projection` for the genuine
orthogonal projection onto any subspace admitting one. The spectral tail
bound is an explicit input and is not asserted to hold for an arbitrary
subspace. -/
theorem orthogonal_projection_alignment (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (Z B : H) (E Λ : ℝ)
    (hE : 0 ≤ E) (hΛ : 0 < Λ)
    (htail : ‖B - K.starProjection B‖ ^ 2 ≤ E / Λ) :
    ⟪Z, B⟫_ℝ - ‖Z‖ * Real.sqrt (E / Λ) ≤
      ‖K.starProjection Z‖ * ‖B‖ := by
  have hq : 0 ≤ E / Λ := div_nonneg hE hΛ.le
  have herror : ‖B - K.starProjection B‖ ≤ Real.sqrt (E / Λ) := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg (E / Λ),
      norm_nonneg (B - K.starProjection B)]
  have hsplit : ⟪Z, B⟫_ℝ =
      ⟪K.starProjection Z, B⟫_ℝ + ⟪Z, B - K.starProjection B⟫_ℝ := by
    rw [inner_sub_right, K.inner_starProjection_left_eq_right Z B]
    ring
  have hleft := real_inner_le_norm (K.starProjection Z) B
  have hright : ⟪Z, B - K.starProjection B⟫_ℝ ≤
      ‖Z‖ * Real.sqrt (E / Λ) :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left herror (norm_nonneg Z))
  linarith

/-- Unit norm specialization of the alignment bound, as displayed after
manuscript `lem:sp-projection`. -/
theorem orthogonal_projection_norm_lower (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (Z B : H) (E Λ : ℝ)
    (hE : 0 ≤ E) (hΛ : 0 < Λ) (hZ : ‖Z‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (htail : ‖B - K.starProjection B‖ ^ 2 ≤ E / Λ) :
    max 0 (⟪Z, B⟫_ℝ - Real.sqrt (E / Λ)) ≤ ‖K.starProjection Z‖ := by
  have halign := orthogonal_projection_alignment K Z B E Λ hE hΛ htail
  have herr : ‖Z‖ * Real.sqrt (E / Λ) ≤ Real.sqrt (E / Λ) := by
    nlinarith [Real.sqrt_nonneg (E / Λ)]
  have hproj : ‖K.starProjection Z‖ * ‖B‖ ≤ ‖K.starProjection Z‖ := by
    nlinarith [norm_nonneg (K.starProjection Z)]
  exact max_le (norm_nonneg _) (by linarith)

/-- A symmetric operator preserving a subspace commutes with its genuine
orthogonal projection. This also proves preservation of the orthogonal
complement, without a separate assumption. -/
theorem orthogonal_projection_commutes (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (S : H →L[ℝ] H)
    (hS : (S : H →ₗ[ℝ] H).IsSymmetric)
    (hinvariant : ∀ x ∈ K, S x ∈ K) (Z : H) :
    K.starProjection (S Z) = S (K.starProjection Z) := by
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
    (hinvariant _ (K.starProjection_apply_mem Z))
  intro w hw
  rw [← map_sub, hS.apply_clm]
  exact K.starProjection_inner_eq_zero Z (S w) (hinvariant w hw)

/-- A norm lower bound on an invariant subspace gives a lower bound on
the correlation of a symmetric operator square for every vector.
The subspace need not be finite dimensional. -/
theorem projected_correlation_lower (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (S : H →L[ℝ] H)
    (hS : (S : H →ₗ[ℝ] H).IsSymmetric)
    (hinvariant : ∀ x ∈ K, S x ∈ K) (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ x ∈ K, c * ‖x‖ ≤ ‖S x‖) (Z : H) :
    c ^ 2 * ‖K.starProjection Z‖ ^ 2 ≤ ⟪Z, S (S Z)⟫_ℝ := by
  have hnorm : ‖S (K.starProjection Z)‖ ≤ ‖S Z‖ := by
    rw [← orthogonal_projection_commutes K S hS hinvariant Z]
    exact K.norm_starProjection_apply_le (S Z)
  have hlow := hlower (K.starProjection Z) (K.starProjection_apply_mem Z)
  have hnon : 0 ≤ c * ‖K.starProjection Z‖ :=
    mul_nonneg hc (norm_nonneg _)
  have hsquared : (c * ‖K.starProjection Z‖) ^ 2 ≤ ‖S Z‖ ^ 2 := by
    nlinarith [norm_nonneg (S Z)]
  simpa only [mul_pow, ← real_inner_self_eq_norm_sq,
    hS.apply_clm Z (S Z)] using hsquared

/-- The correlation conclusion of manuscript `lem:sp-projection` from
the symmetric half-time square, invariance of the low-mode subspace and
the semigroup multiplier lower bound on that subspace.

The multiplier bound and identification of `K` with the generator's
spectral cutoff remain explicit analytic inputs. -/
theorem projected_semigroup_correlation_lower (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (P : ℝ → H →L[ℝ] H) (t Λ : ℝ)
    (hsymmetric : (P (t / 2) : H →ₗ[ℝ] H).IsSymmetric)
    (hsquare : P t = (P (t / 2)).comp (P (t / 2)))
    (hinvariant : ∀ x ∈ K, P (t / 2) x ∈ K)
    (hlower : ∀ x ∈ K,
      Real.exp (-Λ * t / 2) * ‖x‖ ≤ ‖P (t / 2) x‖) (Z : H) :
    Real.exp (-Λ * t) * ‖K.starProjection Z‖ ^ 2 ≤ ⟪Z, P t Z⟫_ℝ := by
  have hexp : Real.exp (-Λ * t / 2) ^ 2 = Real.exp (-Λ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [hexp, hsquare, ContinuousLinearMap.comp_apply] using
    projected_correlation_lower K (P (t / 2)) hsymmetric hinvariant
      (Real.exp (-Λ * t / 2)) (Real.exp_pos _).le hlower Z

end SlowEquilibration
