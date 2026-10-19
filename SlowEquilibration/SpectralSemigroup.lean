-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FrameParseval
public import SlowEquilibration.Correlation
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A genuine diagonal Hilbert-space semigroup

Nonnegative eigenvalues and a countable real Hilbert basis determine bounded
operators on the actual Hilbert space through its isometric identification
with `ℓ²`. Energy is the weighted coefficient series, and form-domain
membership means that this nonnegative series converges. The spherical
Langevin generator and its eigenbasis are separate analytic identifications.
-/

namespace SlowEquilibration.SpectralSemigroup

open scoped InnerProductSpace BigOperators NNReal lp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable section

/-- Coordinate multiplication by a sequence bounded in absolute value by one. -/
def diagonalVector (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1)
    (v : ℓ²(ℕ, ℝ)) : ℓ²(ℕ, ℝ) :=
  ⟨fun j => m j * v j, (lp.memℓp v).mono' (fun j => by
    simp only [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hm j) (abs_nonneg (v j))).trans_eq
      (one_mul _) )⟩

@[simp] theorem diagonalVector_apply (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1)
    (v : ℓ²(ℕ, ℝ)) (j : ℕ) : diagonalVector m hm v j = m j * v j := rfl

theorem diagonalVector_norm_le (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1)
    (v : ℓ²(ℕ, ℝ)) : ‖diagonalVector m hm v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro j
  simp only [diagonalVector_apply, norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hm j) (abs_nonneg (v j))).trans_eq (one_mul _)

/-- The diagonal multiplier as a linear map on `ℓ²`. -/
def diagonalLinear (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1) :
    ℓ²(ℕ, ℝ) →ₗ[ℝ] ℓ²(ℕ, ℝ) where
  toFun := diagonalVector m hm
  map_add' v w := by ext j; simp [mul_add]
  map_smul' c v := by ext j; simp [mul_left_comm]

/-- The diagonal multiplier as an actual bounded continuous linear operator. -/
def diagonal (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1) :
    ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) :=
  (diagonalLinear m hm).mkContinuous 1 (fun v => by
    simpa only [one_mul, diagonalLinear, LinearMap.coe_mk, AddHom.coe_mk]
      using diagonalVector_norm_le m hm v)

@[simp] theorem diagonal_apply (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1)
    (v : ℓ²(ℕ, ℝ)) (j : ℕ) : diagonal m hm v j = m j * v j := rfl

/-- Transport a bounded diagonal multiplier through an actual Hilbert basis. -/
def multiplier (b : HilbertBasis ℕ ℝ H) (m : ℕ → ℝ) (hm : ∀ j, |m j| ≤ 1) :
    H →L[ℝ] H :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((diagonal m hm).comp b.repr.toLinearIsometry.toContinuousLinearMap)

theorem multiplier_apply (b : HilbertBasis ℕ ℝ H) (m : ℕ → ℝ)
    (hm : ∀ j, |m j| ≤ 1) (x : H) :
    multiplier b m hm x = b.repr.symm (diagonal m hm (b.repr x)) := rfl

@[simp] theorem coefficient_multiplier (b : HilbertBasis ℕ ℝ H) (m : ℕ → ℝ)
    (hm : ∀ j, |m j| ≤ 1) (x : H) (j : ℕ) :
    ⟪b j, multiplier b m hm x⟫_ℝ = m j * ⟪b j, x⟫_ℝ := by
  rw [← b.repr_apply_apply, multiplier_apply, b.repr.apply_symm_apply]
  simp [b.repr_apply_apply]

theorem multiplier_norm_le (b : HilbertBasis ℕ ℝ H) (m : ℕ → ℝ)
    (hm : ∀ j, |m j| ≤ 1) (x : H) : ‖multiplier b m hm x‖ ≤ ‖x‖ := by
  rw [multiplier_apply, b.repr.symm.norm_map]
  exact (diagonalVector_norm_le m hm (b.repr x)).trans_eq (b.repr.norm_map x)

theorem multiplier_isSymmetric (b : HilbertBasis ℕ ℝ H) (m : ℕ → ℝ)
    (hm : ∀ j, |m j| ≤ 1) :
    (multiplier b m hm : H →ₗ[ℝ] H).IsSymmetric := by
  intro x y
  change ⟪multiplier b m hm x, y⟫_ℝ = ⟪x, multiplier b m hm y⟫_ℝ
  rw [← b.tsum_inner_mul_inner, ← b.tsum_inner_mul_inner]
  apply tsum_congr
  intro j
  rw [real_inner_comm (b j) (multiplier b m hm x), coefficient_multiplier,
    coefficient_multiplier, real_inner_comm (b j) x]
  ring

/-- A genuine nonnegative diagonal spectrum on a real Hilbert space. -/
structure Data (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  basis : HilbertBasis ℕ ℝ H
  eigenvalue : ℕ → ℝ
  eigenvalue_nonneg : ∀ j, 0 ≤ eigenvalue j

namespace Data

variable (D : Data H)

/-- Actual spectral coefficient. -/
def coefficient (x : H) (j : ℕ) : ℝ := ⟪D.basis j, x⟫_ℝ

/-- Spectral Dirichlet energy; convergence is separately required by `FormDomain`. -/
def energy (x : H) : ℝ := ∑' j, D.eigenvalue j * (D.coefficient x j) ^ 2

/-- The quadratic form domain is convergence of the nonnegative energy series. -/
def FormDomain (x : H) : Prop :=
  Summable (fun j => D.eigenvalue j * (D.coefficient x j) ^ 2)

theorem energy_nonneg (x : H) : 0 ≤ D.energy x :=
  tsum_nonneg (fun j => mul_nonneg (D.eigenvalue_nonneg j) (sq_nonneg _))

theorem heatMultiplier_bound (t : ℝ≥0) (j : ℕ) :
    |Real.exp (-(t : ℝ) * D.eigenvalue j)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (D.eigenvalue_nonneg j)

/-- The nonnegative-time diagonal heat semigroup as actual Hilbert operators. -/
def P (t : ℝ≥0) : H →L[ℝ] H :=
  multiplier D.basis (fun j => Real.exp (-(t : ℝ) * D.eigenvalue j))
    (D.heatMultiplier_bound t)

@[simp] theorem coefficient_P (t : ℝ≥0) (x : H) (j : ℕ) :
    D.coefficient (D.P t x) j =
      Real.exp (-(t : ℝ) * D.eigenvalue j) * D.coefficient x j :=
  coefficient_multiplier _ _ _ _ _

theorem P_norm_le (t : ℝ≥0) (x : H) : ‖D.P t x‖ ≤ ‖x‖ :=
  multiplier_norm_le _ _ _ _

theorem P_isSymmetric (t : ℝ≥0) : (D.P t : H →ₗ[ℝ] H).IsSymmetric :=
  multiplier_isSymmetric _ _ _

theorem coefficient_injective {x y : H}
    (h : ∀ j, D.coefficient x j = D.coefficient y j) : x = y := by
  apply D.basis.repr.injective
  apply lp.ext
  funext j
  simpa only [D.basis.repr_apply_apply, coefficient] using h j

@[simp] theorem P_zero : D.P 0 = ContinuousLinearMap.id ℝ H := by
  ext x
  apply D.coefficient_injective
  intro j
  simp

/-- The operators satisfy the semigroup law on the actual Hilbert space. -/
theorem P_add (s t : ℝ≥0) : D.P (s + t) = (D.P s).comp (D.P t) := by
  ext x
  apply D.coefficient_injective
  intro j
  simp only [ContinuousLinearMap.comp_apply, coefficient_P, NNReal.coe_add]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem P_isSelfAdjoint [CompleteSpace H] (t : ℝ≥0) : IsSelfAdjoint (D.P t) :=
  (D.P_isSymmetric t).isSelfAdjoint

/-- Parseval, with convergence, for the actual spectral coefficients. -/
theorem parseval_hasSum (x : H) :
    HasSum (fun j => (D.coefficient x j) ^ 2) (‖x‖ ^ 2) :=
  hilbert_parseval_hasSum D.basis x

/-- Scalar stationary correlation is the convergent exponential coefficient series. -/
theorem correlation_hasSum (t : ℝ≥0) (x : H) :
    HasSum (fun j => Real.exp (-(t : ℝ) * D.eigenvalue j) *
      (D.coefficient x j) ^ 2) ⟪x, D.P t x⟫_ℝ := by
  convert D.basis.hasSum_inner_mul_inner x (D.P t x) using 1
  ext j
  rw [real_inner_comm (D.basis j) x]
  change _ = D.coefficient x j * D.coefficient (D.P t x) j
  rw [coefficient_P]
  ring

theorem correlation_eq_tsum (t : ℝ≥0) (x : H) :
    ⟪x, D.P t x⟫_ℝ = ∑' j, Real.exp (-(t : ℝ) * D.eigenvalue j) *
      (D.coefficient x j) ^ 2 := (D.correlation_hasSum t x).tsum_eq.symm

theorem correlation_nonneg (t : ℝ≥0) (x : H) : 0 ≤ ⟪x, D.P t x⟫_ℝ := by
  rw [D.correlation_eq_tsum]
  exact tsum_nonneg fun j => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- Parseval for the semigroup displacement; its series converges automatically. -/
theorem displacement_hasSum (t : ℝ≥0) (x : H) :
    HasSum (fun j => (1 - Real.exp (-(t : ℝ) * D.eigenvalue j)) ^ 2 *
      (D.coefficient x j) ^ 2) (‖x - D.P t x‖ ^ 2) := by
  convert D.parseval_hasSum (x - D.P t x) using 1
  ext j
  simp only [coefficient, inner_sub_right]
  have hj := D.coefficient_P t x j
  dsimp only [coefficient] at hj
  rw [hj]
  ring

/-- The displacement energy estimate is derived from the actual convergent
weighted coefficient series, not assumed as a norm-error hypothesis. -/
theorem displacement_energy_le (t : ℝ≥0) (x : H) (hx : D.FormDomain x) :
    ‖x - D.P t x‖ ^ 2 ≤ (t : ℝ) * D.energy x := by
  apply hasSum_le _ (D.displacement_hasSum t x) (hx.hasSum.mul_left (t : ℝ))
  intro j
  have h := SlowEquilibration.one_sub_exp_neg_sq_le ((t : ℝ) * D.eigenvalue j)
    (mul_nonneg t.coe_nonneg (D.eigenvalue_nonneg j))
  rw [← neg_mul] at h
  simpa only [energy, mul_assoc] using
    mul_le_mul_of_nonneg_right h (sq_nonneg (D.coefficient x j))

/-- The positive spectral interval `(0, Λ]`; it excludes zero modes. -/
def lowWeight (Λ : ℝ) (j : ℕ) : ℝ :=
  if 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ then 1 else 0

theorem lowWeight_bound (Λ : ℝ) (j : ℕ) : |D.lowWeight Λ j| ≤ 1 := by
  classical
  unfold lowWeight
  split_ifs <;> norm_num

/-- The actual diagonal spectral cutoff operator. -/
def cutoff (Λ : ℝ) : H →L[ℝ] H :=
  multiplier D.basis (D.lowWeight Λ) (D.lowWeight_bound Λ)

@[simp] theorem coefficient_cutoff (Λ : ℝ) (x : H) (j : ℕ) :
    D.coefficient (D.cutoff Λ x) j = D.lowWeight Λ j * D.coefficient x j :=
  coefficient_multiplier _ _ _ _ _

theorem cutoff_isSymmetric (Λ : ℝ) : (D.cutoff Λ : H →ₗ[ℝ] H).IsSymmetric :=
  multiplier_isSymmetric _ _ _

theorem cutoff_idempotent (Λ : ℝ) (x : H) :
    D.cutoff Λ (D.cutoff Λ x) = D.cutoff Λ x := by
  classical
  apply D.coefficient_injective
  intro j
  simp only [coefficient_cutoff]
  unfold lowWeight
  split_ifs <;> simp

theorem cutoff_isSymmetricProjection (Λ : ℝ) :
    (D.cutoff Λ : H →ₗ[ℝ] H).IsSymmetricProjection := by
  refine ⟨?_, D.cutoff_isSymmetric Λ⟩
  ext x
  exact D.cutoff_idempotent Λ x

/-- The positive low spectral subspace, as a genuine linear-operator range. -/
def lowSubspace (Λ : ℝ) : Submodule ℝ H := (D.cutoff Λ).range

instance lowSubspace_hasOrthogonalProjection (Λ : ℝ) :
    (D.lowSubspace Λ).HasOrthogonalProjection :=
  (D.cutoff_isSymmetricProjection Λ).hasOrthogonalProjection_range

/-- The indicator multiplier is precisely Mathlib's orthogonal projection
onto the actual positive low spectral subspace. -/
theorem cutoff_eq_starProjection (Λ : ℝ) :
    D.cutoff Λ = (D.lowSubspace Λ).starProjection := by
  apply ContinuousLinearMap.coe_injective
  exact (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (D.cutoff_isSymmetricProjection Λ)).2

theorem mem_lowSubspace_iff (Λ : ℝ) (x : H) :
    x ∈ D.lowSubspace Λ ↔ ∀ j,
      ¬(0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ) → D.coefficient x j = 0 := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ j hj
    simp [coefficient_cutoff, lowWeight, hj]
  · intro hx
    refine ⟨x, D.coefficient_injective ?_⟩
    intro j
    by_cases hj : 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ
    · simp [coefficient_cutoff, lowWeight, hj]
    · simp [coefficient_cutoff, lowWeight, hj, hx j hj]

/-- Orthogonality to zero modes is the spectral form of centering. -/
def Centered (x : H) : Prop :=
  ∀ j, D.eigenvalue j = 0 → D.coefficient x j = 0

/-- Convergent Parseval series for the complement of the positive cutoff. -/
theorem cutoff_tail_hasSum (Λ : ℝ) (x : H) :
    HasSum (fun j => if 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ
      then 0 else (D.coefficient x j) ^ 2) (‖x - D.cutoff Λ x‖ ^ 2) := by
  classical
  convert D.parseval_hasSum (x - D.cutoff Λ x) using 1
  ext j
  have hj := D.coefficient_cutoff Λ x j
  dsimp only [coefficient] at hj
  simp only [coefficient, inner_sub_right, hj, lowWeight]
  split_ifs <;> ring

/-- The spectral cutoff tail estimate, derived from convergence of the genuine
energy series. Centering removes zero modes excluded by `(0, Λ]`. -/
theorem cutoff_tail_energy_le (Λ : ℝ) (hΛ : 0 < Λ) (x : H)
    (hx : D.FormDomain x) (hcenter : D.Centered x) :
    ‖x - D.cutoff Λ x‖ ^ 2 ≤ D.energy x / Λ := by
  classical
  apply hasSum_le _ (D.cutoff_tail_hasSum Λ x) (hx.hasSum.div_const Λ)
  intro j
  by_cases hj : 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ
  · simp only [ite_eq_left hj]
    exact div_nonneg (mul_nonneg (D.eigenvalue_nonneg j) (sq_nonneg _)) hΛ.le
  · simp only [ite_eq_right hj]
    by_cases hz : D.eigenvalue j = 0
    · simp [hcenter j hz, hz]
    · have hpos : 0 < D.eigenvalue j :=
        lt_of_le_of_ne (D.eigenvalue_nonneg j) (Ne.symm hz)
      have hbig : Λ ≤ D.eigenvalue j :=
        le_of_not_gt (fun h => hj ⟨hpos, h.le⟩)
      apply (le_div_iff₀ hΛ).2
      nlinarith [sq_nonneg (D.coefficient x j)]

/-- The tail bound for Mathlib's actual orthogonal projection. -/
theorem orthogonal_cutoff_tail_energy_le (Λ : ℝ) (hΛ : 0 < Λ) (x : H)
    (hx : D.FormDomain x) (hcenter : D.Centered x) :
    ‖x - (D.lowSubspace Λ).starProjection x‖ ^ 2 ≤ D.energy x / Λ := by
  rw [← D.cutoff_eq_starProjection]
  exact D.cutoff_tail_energy_le Λ hΛ x hx hcenter

/-- The genuine low spectral subspace is invariant under the semigroup. -/
theorem P_mem_lowSubspace (Λ : ℝ) (t : ℝ≥0) (x : H)
    (hx : x ∈ D.lowSubspace Λ) : D.P t x ∈ D.lowSubspace Λ := by
  rw [D.mem_lowSubspace_iff] at hx ⊢
  intro j hj
  simp only [coefficient_P, hx j hj, mul_zero]

theorem cutoff_P_commute (Λ : ℝ) (t : ℝ≥0) (x : H) :
    D.cutoff Λ (D.P t x) = D.P t (D.cutoff Λ x) := by
  apply D.coefficient_injective
  intro j
  simp only [coefficient_cutoff, coefficient_P]
  ring

/-- The exponential multiplier has its claimed floor on the actual spectral
subspace. This norm bound is derived by comparing convergent Parseval series. -/
theorem P_lowSubspace_norm_lower (Λ : ℝ) (t : ℝ≥0) (x : H)
    (hx : x ∈ D.lowSubspace Λ) :
    Real.exp (-(t : ℝ) * Λ) * ‖x‖ ≤ ‖D.P t x‖ := by
  classical
  have hsupp := (D.mem_lowSubspace_iff Λ x).mp hx
  have hsq : Real.exp (-(t : ℝ) * Λ) ^ 2 * ‖x‖ ^ 2 ≤ ‖D.P t x‖ ^ 2 := by
    apply hasSum_le _ ((D.parseval_hasSum x).mul_left
      (Real.exp (-(t : ℝ) * Λ) ^ 2)) (D.parseval_hasSum (D.P t x))
    intro j
    rw [coefficient_P, mul_pow]
    by_cases hj : 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ
    · have hexp : Real.exp (-(t : ℝ) * Λ) ≤
          Real.exp (-(t : ℝ) * D.eigenvalue j) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hj.2
          (neg_nonpos.mpr t.coe_nonneg))
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_pos _).le hexp 2) (sq_nonneg _)
    · simp [hsupp j hj]
  have hnon : 0 ≤ Real.exp (-(t : ℝ) * Λ) * ‖x‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg x)
  nlinarith [norm_nonneg (D.P t x)]

/-- The floor bound applied to Mathlib's actual orthogonal projection. -/
theorem P_orthogonal_cutoff_norm_lower (Λ : ℝ) (t : ℝ≥0) (x : H) :
    Real.exp (-(t : ℝ) * Λ) * ‖(D.lowSubspace Λ).starProjection x‖ ≤
      ‖D.P t ((D.lowSubspace Λ).starProjection x)‖ :=
  D.P_lowSubspace_norm_lower Λ t _ ((D.lowSubspace Λ).starProjection_apply_mem x)

/-- The spectral correlation lower bound of `lem:sp-projection`, using the
actual positive spectral cutoff and a convergent coefficient comparison. -/
theorem projected_correlation_lower (Λ : ℝ) (t : ℝ≥0) (x : H) :
    Real.exp (-(t : ℝ) * Λ) * ‖(D.lowSubspace Λ).starProjection x‖ ^ 2 ≤
      ⟪x, D.P t x⟫_ℝ := by
  classical
  rw [← D.cutoff_eq_starProjection]
  apply hasSum_le _ ((D.parseval_hasSum (D.cutoff Λ x)).mul_left
    (Real.exp (-(t : ℝ) * Λ))) (D.correlation_hasSum t x)
  intro j
  rw [coefficient_cutoff]
  by_cases hj : 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ
  · simp only [lowWeight, ite_eq_left hj, one_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hj.2
      (neg_nonpos.mpr t.coe_nonneg))
  · simp only [lowWeight, ite_eq_right hj, zero_mul, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- The alignment bound with a genuine spectral tail derived from form-domain
membership. No projection-error estimate is assumed. -/
theorem spectral_projection_alignment (Λ : ℝ) (hΛ : 0 < Λ) (Z B : H)
    (hform : D.FormDomain B) (hcenter : D.Centered B) :
    ⟪Z, B⟫_ℝ - ‖Z‖ * Real.sqrt (D.energy B / Λ) ≤
      ‖(D.lowSubspace Λ).starProjection Z‖ * ‖B‖ :=
  SlowEquilibration.orthogonal_projection_alignment (D.lowSubspace Λ)
    Z B (D.energy B) Λ (D.energy_nonneg B) hΛ
    (D.orthogonal_cutoff_tail_energy_le Λ hΛ B hform hcenter)

/-- The direct correlation estimate of `lem:sp-correlation` for the constructed
semigroup. Its displacement input is proved above from the energy series. -/
theorem direct_correlation_estimate (t : ℝ≥0) (Z B : H)
    (hform : D.FormDomain B) (hZ : ‖Z‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    (max 0 (⟪Z, B⟫_ℝ - Real.sqrt ((t : ℝ) * D.energy B / 2))) ^ 2 ≤
      ⟪Z, D.P t Z⟫_ℝ := by
  have hq : 0 ≤ (t : ℝ) * D.energy B / 2 :=
    div_nonneg (mul_nonneg t.coe_nonneg (D.energy_nonneg B)) (by norm_num)
  have hdis := D.displacement_energy_le (t / 2) B hform
  have herr : ‖B - D.P (t / 2) B‖ ≤ Real.sqrt ((t : ℝ) * D.energy B / 2) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat] at hdis
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg ((t : ℝ) * D.energy B / 2),
      norm_nonneg (B - D.P (t / 2) B)]
  have h := SlowEquilibration.correlation_lower_of_displacement
    (D.P (t / 2)) (D.P_isSymmetric (t / 2)) Z B
    (Real.sqrt ((t : ℝ) * D.energy B / 2)) hZ hB (Real.sqrt_nonneg _) herr
  have hsquare : D.P t Z = D.P (t / 2) (D.P (t / 2) Z) := by
    rw [← ContinuousLinearMap.comp_apply, ← D.P_add, add_halves]
  simpa only [← hsquare] using h

/-- Parseval for differences between two semigroup times. -/
theorem time_difference_hasSum (s t : ℝ≥0) (x : H) :
    HasSum (fun j =>
      (Real.exp (-(s : ℝ) * D.eigenvalue j) -
        Real.exp (-(t : ℝ) * D.eigenvalue j)) ^ 2 * (D.coefficient x j) ^ 2)
      (‖D.P s x - D.P t x‖ ^ 2) := by
  convert D.parseval_hasSum (D.P s x - D.P t x) using 1
  ext j
  have hs := D.coefficient_P s x j
  have ht := D.coefficient_P t x j
  dsimp only [coefficient] at hs ht
  simp only [coefficient, inner_sub_right, hs, ht]
  ring

/-- Strong continuity on the entire nonnegative time half-line, derived by
dominated convergence of the actual Parseval series. No finite-energy
assumption is needed for strong continuity. -/
theorem P_apply_continuous (x : H) : Continuous (fun t : ℝ≥0 => D.P t x) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let f : ℝ≥0 → ℕ → ℝ := fun t j =>
    (Real.exp (-(t : ℝ) * D.eigenvalue j) -
      Real.exp (-(s : ℝ) * D.eigenvalue j)) ^ 2 * (D.coefficient x j) ^ 2
  have hlim : Filter.Tendsto (fun t => ∑' j, f t j) (nhds s) (nhds 0) := by
    have ht := tendsto_tsum_of_dominated_convergence
      (𝓕 := nhds s)
      (D.parseval_hasSum x).summable
      (f := f) (g := fun _ => (0 : ℝ)) ?_ ?_
    · simpa using ht
    · intro j
      have hc : Continuous (fun t : ℝ≥0 => f t j) := by dsimp [f]; fun_prop
      simpa [f] using hc.tendsto s
    · apply Filter.Eventually.of_forall
      intro t j
      dsimp only [f]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hs : Real.exp (-(s : ℝ) * D.eigenvalue j) ≤ 1 :=
        (le_abs_self _).trans (D.heatMultiplier_bound s j)
      have ht : Real.exp (-(t : ℝ) * D.eigenvalue j) ≤ 1 :=
        (le_abs_self _).trans (D.heatMultiplier_bound t j)
      have hdiff : |Real.exp (-(t : ℝ) * D.eigenvalue j) -
          Real.exp (-(s : ℝ) * D.eigenvalue j)| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [Real.exp_pos (-(t : ℝ) * D.eigenvalue j),
          Real.exp_pos (-(s : ℝ) * D.eigenvalue j)]
      have hsq := (sq_le_one_iff_abs_le_one _).mpr hdiff
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hsq : Filter.Tendsto (fun t => ‖D.P t x - D.P s x‖ ^ 2)
      (nhds s) (nhds 0) := by
    convert hlim using 1
    funext t
    exact (D.time_difference_hasSum t s x).tsum_eq.symm
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero]
    using hsqrt

end Data

end

end SlowEquilibration.SpectralSemigroup
