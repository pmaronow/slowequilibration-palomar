-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual smooth scalar localizations of the square and logarithm on
bounded intervals, with derived global derivative bounds. -/
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped NNReal ContDiff
namespace SlowEquilibration.SphericalSmoothScalarLocalizations
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def squareBump (C : ℝ) (hC : 0 ≤ C) : ContDiffBump (0 : ℝ) where
  rIn := C+1
  rOut := C+2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def squareLocalization (C : ℝ) (hC : 0 ≤ C) (r : ℝ) : ℝ := squareBump C hC r*r^2

theorem exists_square_localization (C : ℝ) (hC : 0 ≤ C) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ Φ 0=0 ∧
      (∃ K : ℝ≥0,∀ r,‖deriv Φ r‖ ≤ K) ∧
      ∀ r∈Icc (-C) C,Φ r=r^2 ∧ deriv Φ r=2*r := by
  let Φ := squareLocalization C hC
  have hΦ : ContDiff ℝ ∞ Φ := (squareBump C hC).contDiff.mul (contDiff_id.pow 2)
  have hc : HasCompactSupport Φ := (squareBump C hC).hasCompactSupport.mul_right
  obtain ⟨K0,hK0⟩ := hc.deriv.exists_bound_of_continuous (hΦ.continuous_deriv (by simp))
  refine ⟨Φ,hΦ,by simp [Φ,squareLocalization],⟨⟨max K0 0,le_max_right _ _⟩,
    fun r => (hK0 r).trans (le_max_left _ _)⟩,?_⟩
  intro r hr
  have hball : r∈Metric.ball (0 : ℝ) (squareBump C hC).rIn := by
    simp only [Metric.mem_ball,Real.dist_eq,squareBump,sub_zero]
    have ha : |r|≤C := abs_le.mpr hr
    linarith
  have he : Φ=ᶠ[𝓝 r] (fun x : ℝ => x^2) :=
    ((squareBump C hC).eventuallyEq_one_of_mem_ball hball).mono (fun x hx => by
      simp only [Φ,squareLocalization,hx,Pi.one_apply,one_mul])
  refine ⟨he.self_of_nhds,?_⟩
  rw [he.deriv_eq]
  simp

def logBump (C : ℝ) (hC : 1 ≤ C) : ContDiffBump ((C+1)/2) where
  rIn := (C-1)/2+1/4
  rOut := (C-1)/2+1/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def logLocalization (C : ℝ) (hC : 1 ≤ C) (r : ℝ) : ℝ := logBump C hC r*Real.log r

theorem logLocalization_contDiff (C : ℝ) (hC : 1 ≤ C) :
    ContDiff ℝ ∞ (logLocalization C hC) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r=0
  · subst r
    have hnot : (0 : ℝ)∉tsupport (logBump C hC) := by
      rw [(logBump C hC).tsupport_eq]
      simp only [Metric.mem_closedBall,Real.dist_eq,logBump]
      rw [abs_of_nonpos (by linarith : 0-(C+1)/2 ≤ 0)]
      linarith
    have he := notMem_tsupport_iff_eventuallyEq.mp hnot
    have hz : logLocalization C hC=ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := he.mono
      (fun x hx => by simp only [logLocalization,hx,Pi.zero_apply,zero_mul])
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq hz
  · exact (logBump C hC).contDiffAt.mul (Real.contDiffAt_log.mpr hr)

theorem exists_log_localization (C : ℝ) (hC : 1 ≤ C) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ Φ 0=0 ∧
      (∃ K : ℝ≥0,∀ r,‖deriv Φ r‖ ≤ K) ∧
      ∀ r∈Icc 1 C,Φ r=Real.log r ∧ deriv Φ r=r⁻¹ := by
  let Φ := logLocalization C hC
  have hΦ := logLocalization_contDiff C hC
  have hc : HasCompactSupport Φ := (logBump C hC).hasCompactSupport.mul_right
  obtain ⟨K0,hK0⟩ := hc.deriv.exists_bound_of_continuous (hΦ.continuous_deriv (by simp))
  refine ⟨Φ,hΦ,by simp [Φ,logLocalization],⟨⟨max K0 0,le_max_right _ _⟩,
    fun r => (hK0 r).trans (le_max_left _ _)⟩,?_⟩
  intro r hr
  have hball : r∈Metric.ball ((C+1)/2) (logBump C hC).rIn := by
    simp only [Metric.mem_ball,Real.dist_eq,logBump]
    apply abs_lt.mpr
    constructor <;> linarith [hr.1,hr.2]
  have he : Φ=ᶠ[𝓝 r] Real.log :=
    ((logBump C hC).eventuallyEq_one_of_mem_ball hball).mono (fun x hx => by
      simp only [Φ,logLocalization,hx,Pi.one_apply,one_mul])
  refine ⟨he.self_of_nhds,?_⟩
  rw [he.deriv_eq,Real.deriv_log]

end SlowEquilibration.SphericalSmoothScalarLocalizations
