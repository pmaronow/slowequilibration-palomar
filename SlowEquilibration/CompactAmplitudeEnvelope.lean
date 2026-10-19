-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSStability
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! # The unique-latitude amplitude envelope

For a continuous profile on a compact latitude interval, a unique maximizer
gives the amplitude derivative of the maximized trial. No derivative of
the maximizing latitude and no nondegeneracy assumption are needed.
-/
namespace SlowEquilibration.CompactAmplitudeEnvelope
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [Nonempty E]

/-- An actual attained maximizer of the scalar amplitude trial. -/
def maximizer (φ c : E → ℝ) (hφ : Continuous φ) (hc : Continuous c) (τ : ℝ) : E :=
  Classical.choose (isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    (hφ.add (hc.const_mul (τ*(2+τ)))).continuousOn)

theorem maximizer_property (φ c : E → ℝ) (hφ : Continuous φ) (hc : Continuous c)
    (τ : ℝ) (r : E) :
    φ r+τ*(2+τ)*c r ≤
      φ (maximizer φ c hφ hc τ)+τ*(2+τ)*c (maximizer φ c hφ hc τ) :=
  (Classical.choose_spec (isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    (hφ.add (hc.const_mul (τ*(2+τ)))).continuousOn)).2 (mem_univ r)

/-- The literal maximized amplitude trial. -/
def envelope (φ c : E → ℝ) (hφ : Continuous φ) (hc : Continuous c) (τ : ℝ) : ℝ :=
  φ (maximizer φ c hφ hc τ)+τ*(2+τ)*c (maximizer φ c hφ hc τ)

theorem envelope_zero (φ c : E → ℝ) (hφ : Continuous φ) (hc : Continuous c)
    (r₀ : E) (hmaximum : ∀ r, φ r ≤ φ r₀) : envelope φ c hφ hc 0=φ r₀ := by
  have hmax := maximizer_property φ c hφ hc 0 r₀
  have hle := hmaximum (maximizer φ c hφ hc 0)
  simp only [zero_mul,add_zero] at hmax
  simp only [envelope,zero_mul,add_zero]
  exact le_antisymm hle hmax

/-- Optimizer convergence is derived from the unique original latitude and
the actual uniformly bounded amplitude coefficient. -/
theorem maximizer_tendsto (φ c : E → ℝ) (hφ : Continuous φ) (hc : Continuous c)
    (r₀ : E) (hunique : ∀ r, φ r₀ ≤ φ r → r=r₀) :
    Tendsto (maximizer φ c hφ hc) (𝓝 (0 : ℝ)) (𝓝 r₀) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hbound (r : E) : |c r| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC r (mem_univ r)
  have hid : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0) := tendsto_id
  have hδ : Tendsto (fun τ : ℝ => 2*C*|τ*(2+τ)|) (𝓝 0) (𝓝 0) := by
    have h := ((hid.mul (hid.const_add 2)).abs).const_mul (2*C)
    simpa only [mul_zero,zero_mul,zero_add,abs_zero,id_eq] using h
  apply CSStability.approximate_minimizers_tendsto (fun r => -φ r) hφ.neg r₀
    (fun r h => hunique r (by linarith)) (𝓝 0) (maximizer φ c hφ hc)
    (fun τ => 2*C*|τ*(2+τ)|) hδ
  apply Eventually.of_forall
  intro τ
  let r := maximizer φ c hφ hc τ
  have hm := maximizer_property φ c hφ hc τ r₀
  have hcoeff : |c r-c r₀| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hbound r,hbound r₀])
  have he : (τ*(2+τ))*(c r-c r₀) ≤ 2*C*|τ*(2+τ)| := by
    calc
      _ ≤ |(τ*(2+τ))*(c r-c r₀)| := le_abs_self _
      _ = |τ*(2+τ)| * |c r-c r₀| := abs_mul _ _
      _ ≤ |τ*(2+τ)| * (2*C) := mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)
      _ = _ := by ring
  change -φ r ≤ -φ r₀+2*C*|τ*(2+τ)|
  change φ r₀+τ*(2+τ)*c r₀ ≤ φ r+τ*(2+τ)*c r at hm
  linarith

/-- The scalar envelope derivative has exactly the source factor two,
because the Gaussian amplitude square changes by τ(2+τ). -/
theorem envelope_hasDerivAt (φ c : E → ℝ) (hφ : Continuous φ) (hc : Continuous c)
    (r₀ : E) (hmaximum : ∀ r, φ r ≤ φ r₀)
    (hunique : ∀ r, φ r₀ ≤ φ r → r=r₀) :
    HasDerivAt (envelope φ c hφ hc) (2*c r₀) 0 := by
  have hopt := maximizer_tendsto φ c hφ hc r₀ hunique
  have hcoeff := ((hc.tendsto r₀).comp hopt).sub_const (c r₀)
  have hid : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0) := tendsto_id
  have hbound : Tendsto (fun τ : ℝ => |2+τ| * 
      |c (maximizer φ c hφ hc τ)-c r₀| + |τ| * |c r₀|) (𝓝 0) (𝓝 0) := by
    have h := ((hid.const_add 2).abs.mul hcoeff.abs).add
      (hid.abs.mul_const |c r₀|)
    simpa only [sub_self,abs_zero,mul_zero,zero_mul,add_zero,id_eq,Function.comp_apply] using h
  apply hasDerivAt_iff_tendsto.mpr
  refine squeeze_zero (fun τ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun τ => ?_) hbound
  simp only [sub_zero,smul_eq_mul]
  rw [envelope_zero φ c hφ hc r₀ hmaximum]
  let r := maximizer φ c hφ hc τ
  have hlow := maximizer_property φ c hφ hc τ r₀
  have hupp := hmaximum r
  let e := envelope φ c hφ hc τ-φ r₀-τ*(2+τ)*c r₀
  have he0 : 0 ≤ e := by
    change φ r₀+τ*(2+τ)*c r₀ ≤ envelope φ c hφ hc τ at hlow
    dsimp only [e]
    linarith
  have heupper : e ≤ τ*(2+τ)*(c r-c r₀) := by
    change φ r ≤ φ r₀ at hupp
    dsimp only [e,envelope,r]
    linarith
  have heabs : |e| ≤ |τ*(2+τ)| * |c r-c r₀| := by
    rw [abs_of_nonneg he0]
    exact heupper.trans ((le_abs_self _).trans_eq (abs_mul _ _))
  have heq : envelope φ c hφ hc τ-φ r₀-τ*(2*c r₀)=e+τ^2*c r₀ := by
    dsimp only [e]
    ring
  have hnum : |envelope φ c hφ hc τ-φ r₀-τ*(2*c r₀)| ≤
      |τ| * (|2+τ| * |c r-c r₀| + |τ| * |c r₀|) := by
    rw [heq]
    calc
      _ ≤ |e| + |τ^2*c r₀| := abs_add_le _ _
      _ ≤ |τ*(2+τ)| * |c r-c r₀| + |τ^2*c r₀| := add_le_add heabs le_rfl
      _ = _ := by rw [abs_mul,abs_mul,abs_pow]; ring
  by_cases hτ : τ=0
  · subst τ
    simp
  · have hpos : 0 < |τ| := abs_pos.mpr hτ
    have hb := (div_le_iff₀ hpos).mpr (hnum.trans_eq (mul_comm _ _))
    simpa only [Real.norm_eq_abs,smul_eq_mul,inv_mul_eq_div,r] using hb

end
end SlowEquilibration.CompactAmplitudeEnvelope
