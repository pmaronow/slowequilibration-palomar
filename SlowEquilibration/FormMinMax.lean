-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GraphEigenbasis
public import Mathlib

@[expose] public section

namespace SlowEquilibration.FormMinMax

open Module Set Filter Function
open scoped Topology InnerProductSpace
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {H F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual quadratic form associated with the Hilbert graph inclusion. -/
def formEnergy (J : F →L[ℝ] H) (u : F) : ℝ := ‖u‖^2-‖J u‖^2

/-- Generator eigenweights of the actual resolvent eigenbasis. -/
def weight (μ : ℕ → ℝ) (j : ℕ) : ℝ := (μ j)⁻¹-1

omit [CompleteSpace H] in
theorem parseval_sq_hasSum (b : HilbertBasis ℕ ℝ H) (x : H) :
    HasSum (fun j => (b.repr x j)^2) (‖x‖^2) := by
  have h := b.hasSum_inner_mul_inner x x
  have hterm (j : ℕ) : inner ℝ x (b j)*inner ℝ (b j) x = (b.repr x j)^2 := by
    have hc : inner ℝ (b j) x = b.repr x j := (b.repr_apply_apply x j).symm
    rw [real_inner_comm (b j) x, hc, pow_two]
  simpa only [hterm, real_inner_self_eq_norm_sq] using h

/-- The actual eigenvector preimage in the graph, constructed using the
Hilbert adjoint and its proved nonzero resolvent eigenvalue. -/
def eigenPreimage (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (j : ℕ) : F :=
  (μ j)⁻¹ • J.adjoint (b j)

theorem eigenPreimage_image (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (j : ℕ) :
    J (eigenPreimage J b μ j) = b j := by
  rw [eigenPreimage, map_smul, he, smul_smul, inv_mul_cancel₀ (hμ j).ne', one_smul]

/-- The true first-eigenvector trial space in the actual form domain. -/
def trialSpace (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (k : ℕ) : Submodule ℝ F :=
  Submodule.span ℝ (Set.range (fun i : Fin (k+1) => eigenPreimage J b μ i.val))

theorem trialSpace_finrank (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (k : ℕ) :
    finrank ℝ (trialSpace J b μ k) = k+1 := by
  have hli : LinearIndependent ℝ (fun i : Fin (k+1) => eigenPreimage J b μ i.val) := by
    apply LinearIndependent.of_comp J.toLinearMap
    simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, eigenPreimage_image J b μ hμ he] using
      b.orthonormal.linearIndependent.comp (fun i : Fin (k+1) => i.val) Fin.val_injective
  rw [trialSpace, finrank_span_eq_card hli, Fintype.card_fin]

theorem trialSpace_finiteDimensional (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (μ : ℕ → ℝ) (k : ℕ) : FiniteDimensional ℝ (trialSpace J b μ k) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range _)

/-- The actual finite trial span has no coefficients above its final
eigenvector index. This is proved by span induction. -/
theorem trialSpace_coefficients_zero (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (k : ℕ)
    (u : F) (hu : u ∈ trialSpace J b μ k) {j : ℕ} (hj : k < j) : b.repr (J u) j = 0 := by
  change u ∈ Submodule.span ℝ (Set.range (fun i : Fin (k+1) => eigenPreimage J b μ i.val)) at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [eigenPreimage_image J b μ hμ he, HilbertBasis.repr_apply_apply]
    exact b.orthonormal.inner_eq_zero (by have := i.isLt; omega)
  | zero => simp
  | add u v hu hv ihu ihv =>
    simp only [HilbertBasis.repr_apply_apply] at ihu ihv ⊢
    rw [map_add, inner_add_right, ihu, ihv, add_zero]
  | smul c u hu ihu =>
    simp only [HilbertBasis.repr_apply_apply] at ihu ⊢
    rw [map_smul, inner_smul_right, ihu, mul_zero]

/-- Actual form-energy lower bound after eliminating the first `k`
coefficients, from Parseval and the exact proved graph-energy series. -/
theorem formEnergy_ge_of_first_coefficients_zero (J : F →L[ℝ] H) (hJ : Injective J)
    (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (hmono : Monotone (weight μ))
    (k : ℕ) (u : F) (hz : ∀ j < k, b.repr (J u) j = 0) :
    weight μ k * ‖J u‖^2 ≤ formEnergy J u := by
  have hmass := (parseval_sq_hasSum b (J u)).mul_left (weight μ k)
  have henergy := GraphEigenbasis.graph_energy_hasSum J hJ b μ hμ he u
  change HasSum (fun j => weight μ j*(b.repr (J u) j)^2) (formEnergy J u) at henergy
  have hpoint (j : ℕ) : weight μ k*(b.repr (J u) j)^2 ≤
      weight μ j*(b.repr (J u) j)^2 := by
    by_cases hj : j<k
    · rw [hz j hj]
      simp
    · exact mul_le_mul_of_nonneg_right (hmono (le_of_not_gt hj)) (sq_nonneg _)
  have h := hmass.summable.tsum_le_tsum hpoint henergy.summable
  rwa [hmass.tsum_eq, henergy.tsum_eq] at h

/-- The true first-eigenvector trial space satisfies the matching actual
upper Rayleigh bound. -/
theorem formEnergy_le_on_trialSpace (J : F →L[ℝ] H) (hJ : Injective J)
    (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (hmono : Monotone (weight μ))
    (k : ℕ) (u : F) (hu : u ∈ trialSpace J b μ k) :
    formEnergy J u ≤ weight μ k * ‖J u‖^2 := by
  have hmass := (parseval_sq_hasSum b (J u)).mul_left (weight μ k)
  have henergy := GraphEigenbasis.graph_energy_hasSum J hJ b μ hμ he u
  change HasSum (fun j => weight μ j*(b.repr (J u) j)^2) (formEnergy J u) at henergy
  have hpoint (j : ℕ) : weight μ j*(b.repr (J u) j)^2 ≤
      weight μ k*(b.repr (J u) j)^2 := by
    by_cases hj : j≤k
    · exact mul_le_mul_of_nonneg_right (hmono hj) (sq_nonneg _)
    · rw [trialSpace_coefficients_zero J b μ hμ he k u hu (lt_of_not_ge hj)]
      simp
  have h := henergy.summable.tsum_le_tsum hpoint hmass.summable
  rwa [henergy.tsum_eq, hmass.tsum_eq] at h

/-- The genuine map to the first `k` coefficients of the ordinary L² image. -/
def firstCoefficients (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H) (k : ℕ) : F →ₗ[ℝ] (Fin k → ℝ) where
  toFun u i := inner ℝ (b i.val) (J u)
  map_add' u v := by ext i; simp only [map_add, inner_add_right, Pi.add_apply]
  map_smul' c u := by ext i; simp only [map_smul, inner_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

omit [CompleteSpace H] [CompleteSpace F] in
/-- Dimension alone produces a nonzero trial vector with its first `k`
coefficients zero in every actual `(k+1)`-dimensional form subspace. -/
theorem exists_first_coefficients_zero (J : F →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (k : ℕ) (U : Submodule ℝ F) [FiniteDimensional ℝ U] (hdim : finrank ℝ U = k+1) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ j < k, b.repr (J u) j = 0 := by
  let L := (firstCoefficients J b k).comp U.subtype
  have hk : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hi := LinearMap.ker_eq_bot.mp hbot
    have hdimle := LinearMap.finrank_le_finrank_of_injective hi
    rw [hdim, Module.finrank_fin_fun] at hdimle
    omega
  obtain ⟨u, hu, hu0⟩ := (LinearMap.ker L).ne_bot_iff.mp hk
  refine ⟨u.val, u.property, ?_, ?_⟩
  · intro hz
    exact hu0 (Subtype.ext hz)
  · intro j hj
    have hc := congrFun (LinearMap.mem_ker.mp hu) (⟨j, hj⟩ : Fin k)
    change inner ℝ (b j) (J u.val) = 0 at hc
    rwa [← HilbertBasis.repr_apply_apply] at hc

/-- Genuine finite-dimensional Rayleigh trial bounds in the actual form
domain. Uniform quadratic bounds are equivalent to upper Rayleigh quotient
bounds for every nonzero vector because the inclusion is injective. -/
def RayleighTrialBound (J : F →L[ℝ] H) (k : ℕ) (c : ℝ) : Prop :=
  ∃ U : Submodule ℝ F, FiniteDimensional ℝ U ∧ finrank ℝ U = k+1 ∧
    ∀ u ∈ U, formEnergy J u ≤ c*‖J u‖^2

/-- The ordinary variational min-max value, as the infimum of true upper
Rayleigh bounds over all `(k+1)`-dimensional form-domain trial spaces. -/
def rayleighMinMax (J : F →L[ℝ] H) (k : ℕ) : ℝ := sInf {c | RayleighTrialBound J k c}

/-- Genuine Courant--Fischer min-max for the actual closed Hilbert graph
form and its constructed ordered resolvent eigenbasis. No min-max theorem
or trial-dimension conclusion is assumed. -/
theorem rayleighMinMax_eq_weight (J : F →L[ℝ] H) (hJ : Injective J)
    (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (hmono : Monotone (weight μ)) (k : ℕ) :
    rayleighMinMax J k = weight μ k := by
  have hmem : RayleighTrialBound J k (weight μ k) :=
    ⟨trialSpace J b μ k, trialSpace_finiteDimensional J b μ k,
      trialSpace_finrank J b μ hμ he k,
      formEnergy_le_on_trialSpace J hJ b μ hμ he hmono k⟩
  have hlower : ∀ c, RayleighTrialBound J k c → weight μ k ≤ c := by
    intro c hc
    obtain ⟨U, hU, hdim, hbound⟩ := hc
    let : FiniteDimensional ℝ U := hU
    obtain ⟨u, hu, hu0, hz⟩ := exists_first_coefficients_zero J b k U hdim
    have hlow := formEnergy_ge_of_first_coefficients_zero J hJ b μ hμ he hmono k u hz
    have huJ : J u ≠ 0 := by
      intro hzero
      exact hu0 (hJ (hzero.trans (map_zero J).symm))
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr huJ))).mp
      (hlow.trans (hbound u hu))
  have hbdd : BddBelow {c | RayleighTrialBound J k c} := ⟨weight μ k, fun c hc => hlower c hc⟩
  apply le_antisymm
  · exact csInf_le hbdd hmem
  · exact le_csInf ⟨weight μ k, hmem⟩ (fun c hc => hlower c hc)

end
end SlowEquilibration.FormMinMax
