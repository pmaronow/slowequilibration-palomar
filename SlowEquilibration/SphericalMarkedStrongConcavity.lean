-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemicircleModifiedConcavity
public import SlowEquilibration.SphericalMarkedGlobalLoss
public import SlowEquilibration.SphericalMarkedPrecisionIdentification
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Matrix.PosDef

/-! Source global strong concavity of the actual mixed marked complexity,
and positive definiteness of the literal modified score precision. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set SphericalSequentialRegression
open scoped Matrix
set_option maxHeartbeats 400000

theorem sourceMarkedPrecision_isHermitian (μ : FiniteMixture) (Q : ℝ) :
    (sourceMarkedPrecision μ Q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sourceMarkedPrecision]

theorem sourceMarkedPrecision_posDef (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) (hnp : μ.minDegree < μ.maxDegree) :
    (sourceMarkedPrecision μ Q).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMarkedPrecision_isHermitian μ Q)
  intro v hv
  have hκ := sourceMarkedLeastCurvature_pos μ hQ hd hnp
  have hquad := sourceMarkedPrecision_quadratic_lower μ Q (v 0) (v 1)
  have hnorm : 0 < (v 0)^2+(v 1)^2 := by
    by_contra hn
    have hz0 : v 0=0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
    have hz1 : v 1=0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
    apply hv
    ext i
    fin_cases i <;> assumption
  have hval : star v ⬝ᵥ (sourceMarkedPrecision μ Q *ᵥ v)=
      sourceEnergyCurvature μ Q*(v 0)^2+2*sourceEnergyRadialCross μ Q*v 0*v 1+
        sourceModifiedRadialCurvature μ Q*(v 1)^2 := by
    simp only [sourceMarkedPrecision,dotProduct,Matrix.mulVec,Fin.sum_univ_two,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Pi.star_apply,star_trivial]
    ring
  rw [hval]
  have hp := mul_pos hκ hnorm
  linarith

private theorem remainder_square {A B C : ℝ} (hB : B ≠ 0) (e k : ℝ) :
    A*e^2+2*B*e*k+C*k^2-TwoByTwoLeastCurvature.least A B C*(e^2+k^2)=
      (A-TwoByTwoLeastCurvature.least A B C)*
        (e+B/(A-TwoByTwoLeastCurvature.least A B C)*k)^2 := by
  have hd := (sub_pos.mpr (TwoByTwoLeastCurvature.least_lt_first (A := A) (C := C) hB)).ne'
  have heq := TwoByTwoLeastCurvature.least_equation A B C
  field_simp [hd]
  nlinarith [heq]

/-- Source `lem:mo-concavity(a)`: the actual whole-line complexity plus
half the literal least-eigenvalue norm-square is globally concave. -/
theorem sourceMarkedComplexity_strongly_concave (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    ConcaveOn ℝ univ (fun z : ℝ × ℝ => sourceRadialProfile μ Q z.1 z.2+
      sourceMarkedLeastCurvature μ Q/2*(z.1^2+z.2^2)) := by
  let A := sourceEnergyCurvature μ Q
  let B := sourceEnergyRadialCross μ Q
  let κ := sourceMarkedLeastCurvature μ Q
  let b := Q^2*μ.xi2 Q
  let a := Q*μ.xi1 Q
  have hb : 0 < b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hB : B ≠ 0 := (sourceEnergyRadialCross_neg μ hQ hnp).ne
  have hAk : 0 < A-κ := sub_pos.mpr (TwoByTwoLeastCurvature.least_lt_first hB)
  let radial : (ℝ × ℝ) →ₗ[ℝ] ℝ := (Real.sqrt b)⁻¹ • LinearMap.snd ℝ ℝ ℝ
  let residual : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ+(B/(A-κ)) • LinearMap.snd ℝ ℝ ℝ
  have hF : ConcaveOn ℝ univ (fun z : ℝ × ℝ => SemicirclePotential.modifiedPotential (z.2/Real.sqrt b)) := by
    simpa [radial,Function.comp_def,div_eq_mul_inv,mul_comm] using
      SemicirclePotential.modifiedPotential_concave.comp_linearMap radial
  have hSquare : ConvexOn ℝ univ (fun z : ℝ × ℝ => (z.1+B/(A-κ)*z.2)^2) := by
    simpa [residual,Function.comp_def] using (Even.convexOn_pow (show Even (2 : ℕ) by decide) |>.comp_linearMap residual)
  have hWeighted : ConvexOn ℝ univ (fun z : ℝ × ℝ => (A-κ)/2*(z.1+B/(A-κ)*z.2)^2) := by
    simpa only [smul_eq_mul] using hSquare.smul (show 0 ≤ (A-κ)/2 by positivity)
  have hConcave := (hF.sub hWeighted).add_const (1/2+Real.log (b/a)/2)
  apply hConcave.congr
  intro z _
  have hResidual := remainder_square (A := A) (C := sourceModifiedRadialCurvature μ Q) hB z.1 z.2
  have hSqrt : (z.2/Real.sqrt b)^2/4=(1/(2*b))*z.2^2/2 := by
    rw [div_pow,Real.sq_sqrt hb.le]
    ring
  change SemicirclePotential.modifiedPotential (z.2/Real.sqrt b)-
    (A-κ)/2*(z.1+B/(A-κ)*z.2)^2+(1/2+Real.log (b/a)/2)=
      sourceRadialProfile μ Q z.1 z.2+κ/2*(z.1^2+z.2^2)
  unfold SemicirclePotential.modifiedPotential
  rw [hSqrt]
  change SemicirclePotential.potential (z.2/Real.sqrt b)-(1/(2*b))*z.2^2/2-
      (A-κ)/2*(z.1+B/(A-κ)*z.2)^2+(1/2+Real.log (b/a)/2)=
    1/2+Real.log (b/a)/2-scoreQuadratic μ Q (scorePairEquiv (z.1,z.2))/2+
      SemicirclePotential.potential (z.2/Real.sqrt b)+κ/2*(z.1^2+z.2^2)
  rw [source_scoreQuadratic_precision_form]
  change A*z.1^2+2*B*z.1*z.2+(sourceRadialCurvature μ Q-1/(2*b))*z.2^2-
    κ*(z.1^2+z.2^2)=(A-κ)*(z.1+B/(A-κ)*z.2)^2 at hResidual
  nlinarith

end SlowEquilibration.SphericalMarkedWindows
