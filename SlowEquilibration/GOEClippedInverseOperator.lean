-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalClippedResolventUniform
public import SlowEquilibration.GaussianQuadraticTrace
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! The genuine continuous spectral clipped inverse operator.
Its operator norm is dimension independent and the map is Borel; the
definition uses ordinary Mathlib continuous functional calculus. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def symmetricEntries {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ := (1/2:ℝ) • (W+W.transpose)

lemma symmetricEntries_hermitian {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) :
    (symmetricEntries W).IsHermitian := by
  ext i j
  change (1/2:ℝ)*(W j i+W i j)=(1/2:ℝ)*(W i j+W j i)
  ring

lemma symmetricEntries_continuous (m : ℕ) : Continuous (symmetricEntries (m:=m)) := by
  unfold symmetricEntries
  fun_prop

def clippedInverseFunction (k ρ : ℝ) (z : ℝ) : ℝ := (max ρ (k-z))⁻¹

lemma clippedInverseFunction_continuous (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (clippedInverseFunction k ρ) := by
  unfold clippedInverseFunction
  apply Continuous.inv₀
  · exact continuous_const.max (continuous_const.sub continuous_id)
  · intro z
    exact ne_of_gt (lt_of_lt_of_le hρ (le_max_left _ _))

def clippedInverseOperator {m : ℕ} (k ρ : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) (cfc (clippedInverseFunction k ρ) (symmetricEntries W))

/-- A genuine continuous operator-valued clipped resolvent, with the
literal real symmetric matrix as input and a fixed positive cutoff. -/
theorem clippedInverseOperator_continuous (m : ℕ) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (clippedInverseOperator (m:=m) k ρ) := by
  have hc : Continuous (fun W : Matrix (Fin m) (Fin m) ℝ=>
      cfc (clippedInverseFunction k ρ) (symmetricEntries W)) :=
    Continuous.cfc_of_mem_nhdsSet (s:=univ) (clippedInverseFunction k ρ) (by simp)
      (symmetricEntries_continuous m)
      (fun W=>(symmetricEntries_hermitian W).isSelfAdjoint)
      (clippedInverseFunction_continuous k hρ).continuousOn
  exact ((Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp hc

theorem clippedInverseOperator_measurable (m : ℕ) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Measurable (clippedInverseOperator (m:=m) k ρ) :=
  (clippedInverseOperator_continuous m k hρ).measurable

/-- Actual clipped inverse operator norm, without a dimension factor. -/
theorem clippedInverseOperator_norm_le {m : ℕ} (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    ‖clippedInverseOperator k ρ W‖ ≤ ρ⁻¹ := by
  change ‖(Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) (cfc (clippedInverseFunction k ρ) (symmetricEntries W))‖ ≤ _
  rw [← Matrix.cstar_norm_def]
  apply norm_cfc_le (inv_nonneg.mpr hρ.le)
  intro z hz
  unfold clippedInverseFunction
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hρ (le_max_left _ _)))]
  simpa only [one_div] using one_div_le_one_div_of_le hρ (le_max_left ρ (k-z))

theorem clippedInverseOperator_symmetric {m : ℕ} (k ρ : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    (clippedInverseOperator k ρ W).toLinearMap.IsSymmetric := by
  change (Matrix.toEuclideanLin (cfc (clippedInverseFunction k ρ) (symmetricEntries W))).IsSymmetric
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (show (cfc (clippedInverseFunction k ρ) (symmetricEntries W)).IsHermitian from
      IsSelfAdjoint.cfc.isHermitian)

end
end SlowEquilibration.GOEClippedResolvent

