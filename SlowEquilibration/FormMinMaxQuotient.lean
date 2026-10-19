-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FormMinMax

@[expose] public section

namespace SlowEquilibration.FormMinMax

open Module Set Function
open scoped InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {H F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The ordinary actual Rayleigh quotient, with the inclusion mapping the
form-domain vector to its ordinary Hilbert-space value. -/
def rayleighQuotient (J : F →L[ℝ] H) (u : F) : ℝ := formEnergy J u / ‖J u‖^2

omit [CompleteSpace H] [CompleteSpace F] in
/-- The min-max trial bound is precisely a uniform bound on the ordinary
Rayleigh quotient of every nonzero trial vector. -/
theorem rayleighTrialBound_iff_quotient (J : F →L[ℝ] H) (hJ : Injective J)
    (k : ℕ) (c : ℝ) :
    RayleighTrialBound J k c ↔
      ∃ U : Submodule ℝ F, FiniteDimensional ℝ U ∧ finrank ℝ U = k+1 ∧
        ∀ u ∈ U, u ≠ 0 → rayleighQuotient J u ≤ c := by
  have hpos (u : F) (hu : u ≠ 0) : 0 < ‖J u‖^2 := by
    have huJ : J u ≠ 0 := by
      intro hz
      exact hu (hJ (hz.trans (map_zero J).symm))
    exact sq_pos_of_pos (norm_pos_iff.mpr huJ)
  constructor
  · rintro ⟨U, hU, hdim, hbound⟩
    refine ⟨U, hU, hdim, fun u hu hu0 => ?_⟩
    exact (div_le_iff₀ (hpos u hu0)).mpr (hbound u hu)
  · rintro ⟨U, hU, hdim, hbound⟩
    refine ⟨U, hU, hdim, fun u hu => ?_⟩
    by_cases hu0 : u = 0
    · simp only [hu0, formEnergy, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        sub_self, mul_zero, le_refl]
    · exact (div_le_iff₀ (hpos u hu0)).mp (hbound u hu hu0)

omit [CompleteSpace H] [CompleteSpace F] in
/-- A form subspace of dimension larger than `k` contains a genuine
nonzero vector with its first `k` Hilbert coefficients zero. -/
theorem exists_first_coefficients_zero_of_finrank_gt (J : F →L[ℝ] H)
    (b : HilbertBasis ℕ ℝ H) (k : ℕ) (U : Submodule ℝ F)
    [FiniteDimensional ℝ U] (hdim : k < finrank ℝ U) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ j < k, b.repr (J u) j = 0 := by
  let L := (firstCoefficients J b k).comp U.subtype
  have hk : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hi := LinearMap.ker_eq_bot.mp hbot
    have hdimle := LinearMap.finrank_le_finrank_of_injective hi
    rw [Module.finrank_fin_fun] at hdimle
    omega
  obtain ⟨u, hu, hu0⟩ := (LinearMap.ker L).ne_bot_iff.mp hk
  refine ⟨u.val, u.property, ?_, ?_⟩
  · intro hz
    exact hu0 (Subtype.ext hz)
  · intro j hj
    have hc := congrFun (LinearMap.mem_ker.mp hu) (⟨j, hj⟩ : Fin k)
    change inner ℝ (b j) (J u.val) = 0 at hc
    rwa [← HilbertBasis.repr_apply_apply] at hc

/-- An actual finite-dimensional form trial space with Rayleigh bound
strictly below the `k`th actual eigenvalue has dimension at most `k`.
This dimension bound is a conclusion of coefficient elimination and the
proved form-energy series. -/
theorem finrank_le_of_rayleigh_bound_lt (J : F →L[ℝ] H) (hJ : Injective J)
    (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (hmono : Monotone (weight μ))
    (k : ℕ) (c : ℝ) (hc : c < weight μ k) (U : Submodule ℝ F)
    [FiniteDimensional ℝ U] (hbound : ∀ u ∈ U, formEnergy J u ≤ c*‖J u‖^2) :
    finrank ℝ U ≤ k := by
  by_contra hn
  obtain ⟨u, hu, hu0, hz⟩ :=
    exists_first_coefficients_zero_of_finrank_gt J b k U (lt_of_not_ge hn)
  have hlow := formEnergy_ge_of_first_coefficients_zero J hJ b μ hμ he hmono k u hz
  have huJ : J u ≠ 0 := by
    intro hzero
    exact hu0 (hJ (hzero.trans (map_zero J).symm))
  have hle : weight μ k ≤ c :=
    (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr huJ))).mp
      (hlow.trans (hbound u hu))
  exact (not_le_of_gt hc) hle

end
end SlowEquilibration.FormMinMax
