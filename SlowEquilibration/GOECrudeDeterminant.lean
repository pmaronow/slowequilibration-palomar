-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCrudeDeterminant
public import SlowEquilibration.CanonicalGOERealization
public import SlowEquilibration.GOEPhysicalPotential

/-! Global radial-tail determinant control under the manuscript's actual
upper-triangle product-Gaussian GOE law, all dimensions m≤N and all real shifts. -/

@[expose] public section
namespace SlowEquilibration.GOECrudeDeterminant

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
open GaussianCrudeDeterminant CanonicalGOERealization GOESharpMoments GOEPhysicalPotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Positive-dimensional physical GOE: true ordinary integrability and a
uniform operator-edge based exponential majorant for every real shift. -/
theorem physical_crude_mean (n N : ℕ) (hMN : n+1 ≤ N) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n+1) N b) ∧
    physicalMean n N b k ≤ Real.exp ((N:ℝ)*(crudeConstant b+|k|)) := by
  have hN : 0 < N := by omega
  let W := realization (n+1) N b
  have ht := realization_crude_mean W (realization_symmetric _ _ _) hMN hb
    (realization_norm_le _ _ _) k
  have hL := matrix_realization_hasLaw (n+1) hN hb.le
  have hInt : Integrable (fun z => matrixAbsoluteDet n k (GOEAsymptotics.gaussianToMatrix (W z)))
      (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex (n+1))) := by
    simpa only [GaussianMatrixMomentLaw.rawDet,zero_add,matrixAbsoluteDet] using ht.1
  constructor
  · rw [← hL.map_eq]
    exact (integrable_map_measure (matrixAbsoluteDet_measurable n k).aestronglyMeasurable
      hL.aemeasurable).mpr hInt
  · have he := hL.integral_comp (matrixAbsoluteDet_measurable n k).aestronglyMeasurable
    have he' : (∫ z,GaussianMatrixMomentLaw.rawDet 0 k (W z)
        ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex (n+1)))=physicalMean n N b k := by
      simpa only [GaussianMatrixMomentLaw.rawDet,zero_add,matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet,Function.comp_apply,physicalMean,W] using he
    rw [← he']
    exact ht.2

/-- Literal finite-matrix law statement, also including the empty matrix.
The constant C_b=log2+2√b+b is independent of m,N and k. -/
theorem goe_crude_mean (m N : ℕ) (hMN : m ≤ N) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    Integrable (fun W : Matrix (Fin m) (Fin m) ℝ => |(k • 1-W).det|)
      (SphericalGaussianJet.goeLaw m N b) ∧
    (∫ W : Matrix (Fin m) (Fin m) ℝ,|(k • 1-W).det| ∂SphericalGaussianJet.goeLaw m N b) ≤
      Real.exp ((N:ℝ)*(crudeConstant b+|k|)) := by
  cases m with
  | zero =>
    have hf : (fun W : Matrix (Fin 0) (Fin 0) ℝ => |(k • 1-W).det|)=fun _ => (1:ℝ) := by
      funext W
      simp
    rw [hf]
    constructor
    · exact integrable_const _
    · have hc : 0 ≤ crudeConstant b+|k| := by
        unfold crudeConstant
        have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      simp only [integral_const,probReal_univ,smul_eq_mul,mul_one]
      exact Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg N) hc)
  | succ n =>
    exact physical_crude_mean n N hMN hb k

end
end SlowEquilibration.GOECrudeDeterminant
