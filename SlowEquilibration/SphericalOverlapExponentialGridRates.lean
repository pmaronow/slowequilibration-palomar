-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOverlapExponentialGridGeometry

/-! Explicit exponential-horizon decay of the actual finite grid union error. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalOverlapExponential
open Filter
open scoped NNReal Topology
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def exponentialGridHorizon (γ : ℝ) (N : ℕ) : ℝ≥0 :=
  ⟨Real.exp ((N : ℝ)*γ),Real.exp_nonneg _⟩

def exponentialGridError (T : ℝ≥0) (γ c : ℝ) (N : ℕ) : ℝ :=
  (gridSize (exponentialGridHorizon γ N) T : ℝ)*2*Real.exp (-(N : ℝ)*c)

theorem exponentialGridError_bound (T : ℝ≥0) (_hT : 0 < T) (γ c : ℝ)
    (hγ : 0 ≤ γ) (N : ℕ) :
    exponentialGridError T γ c N ≤ (2/(T : ℝ)+4)*Real.exp (-(N : ℝ)*(c-γ)) := by
  have hgrid := gridSize_upper (exponentialGridHorizon γ N) T
  have he : Real.exp ((N : ℝ)*γ)*Real.exp (-(N : ℝ)*c)=
      Real.exp (-(N : ℝ)*(c-γ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp (-(N : ℝ)*c) ≤ Real.exp (-(N : ℝ)*(c-γ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  change (gridSize (exponentialGridHorizon γ N) T : ℝ)*2*Real.exp (-(N : ℝ)*c) ≤ _
  calc
    _ ≤ (Real.exp ((N : ℝ)*γ)/(T : ℝ)+2)*2*Real.exp (-(N : ℝ)*c) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_right hgrid (by norm_num)
    _ = (2/(T : ℝ))*(Real.exp ((N : ℝ)*γ)*Real.exp (-(N : ℝ)*c))+4*Real.exp (-(N : ℝ)*c) := by ring
    _ = (2/(T : ℝ))*Real.exp (-(N : ℝ)*(c-γ))+4*Real.exp (-(N : ℝ)*c) := by rw [he]
    _ ≤ (2/(T : ℝ)+4)*Real.exp (-(N : ℝ)*(c-γ)) := by nlinarith [hs]

theorem exponentialGridError_tendsto_zero (T : ℝ≥0) (hT : 0 < T)
    (γ c : ℝ) (hγ : 0 ≤ γ) (hgap : γ < c) :
    Tendsto (exponentialGridError T γ c) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hgap))
  have hb : Tendsto (fun N : ℕ => (2/(T : ℝ)+4)*Real.exp (-(N : ℝ)*(c-γ))) atTop (𝓝 0) := by
    convert he.const_mul (2/(T : ℝ)+4) using 1
    · funext N
      dsimp only [Function.comp_def]
      congr 1
      ring
    · simp
  apply squeeze_zero (fun N => ?_) (fun N => exponentialGridError_bound T hT γ c hγ N) hb
  dsimp only [exponentialGridError]
  positivity

end SlowEquilibration.SphericalOverlapExponential
