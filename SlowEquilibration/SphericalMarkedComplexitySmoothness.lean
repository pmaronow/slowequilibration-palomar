-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedContactGradient
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual infinite differentiability of the source marked complexity in
the positive exterior spectral region, derived from the literal potential. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter SphericalSequentialRegression
open scoped Topology ContDiff
set_option maxHeartbeats 300000

theorem source_semicirclePotential_contDiffAt {z : ℝ} (hz : 2 < z) :
    ContDiffAt ℝ ∞ SemicirclePotential.potential z := by
  have hDisc : 0 < z^2-4 := by nlinarith
  have hPoly : ContDiffAt ℝ ∞ (fun t : ℝ => t^2-4) z := by fun_prop
  have hRoot := hPoly.sqrt hDisc.ne'
  have hLogPos : 0 < (z+Real.sqrt (z^2-4))/2 := by positivity
  have hLog := ((contDiffAt_id.add hRoot).div_const 2).log hLogPos.ne'
  have hC : ContDiffAt ℝ ∞ (fun _ : ℝ => (1/2 : ℝ)) z := contDiffAt_const
  have hPowDiv : ContDiffAt ℝ ∞ (fun t : ℝ => t^2/4) z := by fun_prop
  have hMul : ContDiffAt ℝ ∞ (fun t : ℝ => t*Real.sqrt (t^2-4)/4) z :=
    (contDiffAt_id.mul hRoot).div_const 4
  have hExplicit : ContDiffAt ℝ ∞ (fun t : ℝ => t^2/4-1/2-t*Real.sqrt (t^2-4)/4+
      Real.log ((t+Real.sqrt (t^2-4))/2)) z :=
    ((hPowDiv.sub hC).sub hMul).add hLog
  apply hExplicit.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hz] with t ht
  exact SemicirclePotential.potential_explicit ht

theorem sourceMarkedComplexity_contDiffAt (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => sourceRadialProfile μ Q z.1 z.2) (e,k) := by
  let s := Real.sqrt (Q^2*μ.xi2 Q)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))
  have hz : 2 < k/s := (lt_div_iff₀ hs).mpr hk
  have hQPoly : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => scoreQuadratic μ Q (scorePairEquiv (z.1,z.2))) (e,k) := by
    simp_rw [source_scoreQuadratic_precision_form]
    fun_prop
  have hScale : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => z.2/s) (e,k) := by fun_prop
  have hPotential := (source_semicirclePotential_contDiffAt hz).comp (e,k) hScale
  change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
    scoreQuadratic μ Q (scorePairEquiv (z.1,z.2))/2+SemicirclePotential.potential (z.2/s)) (e,k)
  exact (contDiffAt_const.sub (hQPoly.div_const 2)).add hPotential

end SlowEquilibration.SphericalMarkedWindows
