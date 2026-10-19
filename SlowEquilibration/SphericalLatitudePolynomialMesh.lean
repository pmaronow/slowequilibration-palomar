-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeGridConcentration
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# A literal polynomial mesh for the actual tensor latitude process

The true number of tensor coordinates is polynomial in dimension. A concrete
polynomial latitude mesh therefore makes the full continuity error bounded
independently of dimension, while preserving the exponential Gaussian tails.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem tensorCoordinate_card_le {N : ℕ} (hN : 1 ≤ N) (P : ℕ) :
    Fintype.card (Coordinate N P) ≤ (P+1)*N^P := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _p : Degree P, N^P := by
      apply Finset.sum_le_sum
      intro p _
      simp only [SphericalAging.FiniteModel.TensorIndex,Fintype.card_fun,Fintype.card_fin]
      exact Nat.pow_le_pow_right hN (by omega)
    _ = Fintype.card (Degree P)*N^P := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by
      simpa using Fintype.card_subtype_le (fun p : Fin (P+1) => 2 ≤ p.val))

theorem sqrt_tensorCoordinate_card_le {N : ℕ} (hN : 1 ≤ N) (P : ℕ) :
    Real.sqrt (Fintype.card (Coordinate N P) : ℝ) ≤ ((P+1 : ℕ) : ℝ)*(N : ℝ)^P := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcard : (Fintype.card (Coordinate N P) : ℝ) ≤ ((P+1 : ℕ) : ℝ)*(N : ℝ)^P := by
    exact_mod_cast tensorCoordinate_card_le hN P
  have hone : (1 : ℝ) ≤ ((P+1 : ℕ) : ℝ)*(N : ℝ)^P := by
    have hpow : (1 : ℝ) ≤ (N : ℝ)^P := one_le_pow₀ hNr
    have hP : (1 : ℝ) ≤ ((P+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ P+1 by omega)
    nlinarith
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card (Coordinate N P) by positivity)
  have hnon := Real.sqrt_nonneg (Fintype.card (Coordinate N P) : ℝ)
  nlinarith

def latitudeMeshSize (n P : ℕ) : ℕ := (n+1)^(2*(P+2))

theorem latitudeMeshSize_pos (n P : ℕ) : 1 ≤ latitudeMeshSize n P := by
  unfold latitudeMeshSize
  exact Nat.one_le_pow _ _ (by omega)

theorem sqrt_latitudeMeshSize (n P : ℕ) :
    Real.sqrt (latitudeMeshSize n P : ℝ) = (((n+1 : ℕ) : ℝ))^(P+2) := by
  unfold latitudeMeshSize
  rw [Nat.cast_pow,Nat.mul_comm 2 (P+2),pow_mul,Real.sqrt_sq (by positivity)]

theorem latitudeMesh_radius_le (n P : ℕ) {a b : ℝ}
    (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    Real.sqrt ((b-a)/(latitudeMeshSize n P : ℝ)) ≤ 2/(((n+1 : ℕ) : ℝ)^(P+2)) := by
  rw [Real.sqrt_div (sub_nonneg.mpr hab),sqrt_latitudeMeshSize]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs := Real.sq_sqrt (sub_nonneg.mpr hab)
  have hn := Real.sqrt_nonneg (b-a)
  nlinarith

/-- The actual continuity error of the selected polynomial mesh is bounded
by an explicit dimension-independent constant. -/
theorem latitude_polynomial_mesh_error_le (n P : ℕ) (c : Degree P → ℝ) (β : ℝ)
    {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    latitudeModulusScale n c β*
      (2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+Real.sqrt ((n+1 : ℕ) : ℝ))*
        Real.sqrt ((b-a)/(latitudeMeshSize n P : ℝ)) ≤
      4 * |β| * Real.sqrt (spatialVariance c)*(2*((P+1 : ℕ) : ℝ)+1) := by
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ n+1 by omega)
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hsN : Real.sqrt N ≤ N := by
    nlinarith [Real.sq_sqrt hN0.le,Real.sqrt_nonneg N]
  have hpow : N^P ≤ N^(P+1) := pow_le_pow_right₀ hN (by omega)
  have hpow' : N ≤ N^(P+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hN (show 1 ≤ P+1 by omega)
  have hcN := sqrt_tensorCoordinate_card_le (show 1 ≤ n+1 by omega) P
  have hnorm : 2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+Real.sqrt N ≤
      (2*((P+1 : ℕ) : ℝ)+1)*N^(P+1) := by
    change Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ) ≤ ((P+1 : ℕ) : ℝ)*N^P at hcN
    have hm := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ ((P+1 : ℕ) : ℝ) by positivity)
    nlinarith
  have hscale : latitudeModulusScale n c β ≤ 2 * |β| * Real.sqrt (spatialVariance c)*N := by
    unfold latitudeModulusScale
    exact mul_le_mul_of_nonneg_left hsN (by positivity)
  have herr := latitudeMesh_radius_le n P ha hb hab
  calc
    _ ≤ (2 * |β| * Real.sqrt (spatialVariance c)*N)*
        ((2*((P+1 : ℕ) : ℝ)+1)*N^(P+1))*(2/N^(P+2)) := by
      apply mul_le_mul
      · exact mul_le_mul hscale hnorm (by positivity) (by positivity)
      · exact herr
      · positivity
      · positivity
    _ = _ := by
      rw [show P+2=(P+1)+1 by omega,pow_succ]
      field_simp
      simp only [pow_succ]
      ring

/-- A polynomial number of actual mesh tails is absorbed into one
exponential tail, with an explicitly positive decay rate. -/
theorem latitude_polynomial_tail_eventually_le (d : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      Real.exp (-(((n+1 : ℕ) : ℝ))/2)+
        2*((((n+1 : ℕ) : ℝ))^d+1)*Real.exp (-α*((n+1 : ℕ) : ℝ)) ≤
          Real.exp (-γ*((n+1 : ℕ) : ℝ)) := by
  let γ : ℝ := min (1/4) (α/2)
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  have hδ : 0 < 1/2-γ := by have := min_le_left (1/4 : ℝ) (α/2); dsimp [γ]; linarith
  have hη : 0 < α-γ := by have := min_le_right (1/4 : ℝ) (α/2); dsimp [γ]; linarith
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexp {a : ℝ} (ha : 0 < a) :
      Tendsto (fun n : ℕ => Real.exp (-a*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop ha) using 1
    ext n
    simp only [Function.comp_apply,neg_mul]
  have hpoly : Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ))^d*
      Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) (α-γ) hη).comp hN using 1
    ext n
    simp only [Function.comp_apply,Real.rpow_natCast]
  have hr : Tendsto (fun n : ℕ => Real.exp (-(1/2-γ)*((n+1 : ℕ) : ℝ))+
      2*((((n+1 : ℕ) : ℝ))^d*Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ))+
        Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ)))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using (hexp hδ).add ((hpoly.add (hexp hη)).const_mul 2)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ)<1 by norm_num))] with n hn
  have e₁ : Real.exp (-(((n+1 : ℕ) : ℝ))/2) =
      Real.exp (-(1/2-γ)*((n+1 : ℕ) : ℝ))*Real.exp (-γ*((n+1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e₂ : Real.exp (-α*((n+1 : ℕ) : ℝ)) =
      Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ))*Real.exp (-γ*((n+1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hn.le (Real.exp_nonneg (-γ*((n+1 : ℕ) : ℝ)))
  rw [one_mul] at hm
  rw [e₁,e₂]
  nlinarith

end SlowEquilibration.SphericalModel
