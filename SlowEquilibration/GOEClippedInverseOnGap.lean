-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedInverseTrace

/-! On the actual outside-spectrum event the genuine continuous clipped
operator equals the ordinary inverse of the literal shifted matrix. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Equality to the true ordinary shifted inverse on the stated spectral
gap; the conclusion is derived from actual functional calculus products. -/
theorem clippedInverseOperator_eq_inverse_of_spectral_gap {m : ℕ} (k : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (W : Matrix (Fin m) (Fin m) ℝ)
    (hgap : ∀ z ∈ spectrum ℝ (symmetricEntries W),ρ ≤ k-z) :
    clippedInverseOperator k ρ W=
      (k • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))-
        (Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) (symmetricEntries W)).inverse := by
  let A:=symmetricEntries W
  let f : ℝ → ℝ:=fun z=>k-z
  let g:=clippedInverseFunction k ρ
  have hA : IsSelfAdjoint A:=(symmetricEntries_hermitian W).isSelfAdjoint
  have hf : Continuous f:=continuous_const.sub continuous_id
  have hg : Continuous g:=clippedInverseFunction_continuous k hρ
  have hfg : cfc (fun z=>f z*g z) A=1 := by
    rw [← cfc_const_one ℝ A]
    apply cfc_congr
    intro z hz
    change (k-z)*(max ρ (k-z))⁻¹=1
    rw [max_eq_right (hgap z hz)]
    exact mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le hρ (hgap z hz)))
  have hgf : cfc (fun z=>g z*f z) A=1 := by
    convert hfg using 1
    congr 1
    funext z
    exact mul_comm _ _
  have hlin : cfc f A=k • (1:Matrix (Fin m) (Fin m) ℝ)-A := by
    change cfc (fun z=>(fun _=>k) z-id z) A=_
    rw [cfc_sub (fun _ : ℝ=>k) id A continuous_const.continuousOn continuous_id.continuousOn,
      cfc_const k A hA,cfc_id ℝ A hA]
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [cfc_mul f g A hf.continuousOn hg.continuousOn,hlin] at hfg
  rw [cfc_mul g f A hg.continuousOn hf.continuousOn,hlin] at hgf
  let T:=k • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))-
    (Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) A
  let S:=clippedInverseOperator k ρ W
  have hTS : T*S=1 := by
    have hh:=congrArg (Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) hfg
    simpa only [map_mul,map_sub,map_smul,map_one,T,S,clippedInverseOperator,A,g,
      ContinuousLinearMap.one_def] using hh
  have hST : S*T=1 := by
    have hh:=congrArg (Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) hgf
    simpa only [map_mul,map_sub,map_smul,map_one,T,S,clippedInverseOperator,A,g,
      ContinuousLinearMap.one_def] using hh
  have hunit : IsUnit T:=isUnit_iff_exists.mpr ⟨S,hTS,hST⟩
  change S=T.inverse
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  apply hunit.mul_right_cancel
  rw [hST,Ring.inverse_mul_cancel T hunit]

/-- A literal operator norm good event implies the spectral gap and hence
the clipped/ordinary inverse equality. The physical GOE edge theorem
supplies such events with exponentially small complement. -/
theorem clippedInverseOperator_eq_inverse_of_norm_gap (n : ℕ) (k : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hgap : ‖(Matrix.toEuclideanCLM (n:=Fin (n+1)) (𝕜:=ℝ)) (symmetricEntries W)‖ ≤ k-ρ) :
    clippedInverseOperator k ρ W=
      (k • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n+1)))-
        (Matrix.toEuclideanCLM (n:=Fin (n+1)) (𝕜:=ℝ)) (symmetricEntries W)).inverse := by
  apply clippedInverseOperator_eq_inverse_of_spectral_gap k hρ W
  intro z hz
  have hzN:=spectrum.norm_le_norm_of_mem hz
  rw [Matrix.cstar_norm_def,Real.norm_eq_abs] at hzN
  linarith [le_abs_self z]

end
end SlowEquilibration.GOEClippedResolvent

