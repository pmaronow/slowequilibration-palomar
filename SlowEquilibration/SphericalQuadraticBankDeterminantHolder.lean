-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.WeightedTraceMean

@[expose] public section

/-! The normalized Cauchy step in source `mb-quadratic`, formulated so the
integrability required by the subsequent physical Palm Tonelli argument is
part of the conclusion. -/

namespace SlowEquilibration.SphericalQuadraticBankDeterminantHolder
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

/-- If the determinant and quadratic-bank partition have controlled
normalized second moments, then their dependent product has a genuine
integrable expectation bounded by the product of their own means. -/
theorem determinant_quadratic_bank_cauchy
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (D Z : Ω → ℝ)
    {d m K C : ℝ} (hd : 0 < d) (hm : 0 < m)
    (hD0 : ∀ ω, 0 ≤ D ω) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hDlp : MemLp (fun ω => D ω/d) 2 ν)
    (hZlp : MemLp (fun ω => Z ω/m) 2 ν)
    (hDm : (∫ ω, (D ω/d)^2 ∂ν) ≤ K)
    (hZm : (∫ ω, (Z ω/m)^2 ∂ν) ≤ C) :
    Integrable (fun ω => D ω*Z ω) ν ∧
      (∫ ω, D ω*Z ω ∂ν) ≤ d*m*Real.sqrt K*Real.sqrt C := by
  let dN := fun ω => D ω/d
  let zN := fun ω => Z ω/m
  have hprod : Integrable (fun ω => dN ω*zN ω) ν :=
    memLp_one_iff_integrable.mp (hDlp.mul hZlp)
  have hfactor : (fun ω => D ω*Z ω) =
      fun ω => (d*m)*(dN ω*zN ω) := by
    funext ω
    dsimp [dN,zN]
    field_simp [hd.ne',hm.ne']
  have hDz : Integrable (fun ω => D ω*Z ω) ν := by
    rw [hfactor]
    exact hprod.const_mul _
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 by
      rw [Real.holderConjugate_iff]
      norm_num)
    (ae_of_all ν fun ω => div_nonneg (hD0 ω) hd.le)
    (ae_of_all ν fun ω => div_nonneg (hZ0 ω) hm.le)
    (by simpa [dN] using hDlp)
    (by simpa [zN] using hZlp)
  have hCS' : (∫ ω, dN ω*zN ω ∂ν) ≤
      Real.sqrt (∫ ω, (dN ω)^2 ∂ν) *
        Real.sqrt (∫ ω, (zN ω)^2 ∂ν) := by
    simpa only [Real.rpow_two, ←Real.sqrt_eq_rpow] using hCS
  have hbound : (∫ ω, dN ω*zN ω ∂ν) ≤
      Real.sqrt K*Real.sqrt C := by
    calc
      _ ≤ Real.sqrt (∫ ω, (dN ω)^2 ∂ν) *
          Real.sqrt (∫ ω, (zN ω)^2 ∂ν) := hCS'
      _ ≤ Real.sqrt K*Real.sqrt C := by
        gcongr
  refine ⟨hDz,?_⟩
  calc
    (∫ ω, D ω*Z ω ∂ν) =
        (d*m)*(∫ ω, dN ω*zN ω ∂ν) := by
          rw [hfactor,integral_const_mul]
    _ ≤ (d*m)*(Real.sqrt K*Real.sqrt C) :=
      mul_le_mul_of_nonneg_left hbound (mul_pos hd hm).le
    _ = d*m*Real.sqrt K*Real.sqrt C := by ring

end
end SlowEquilibration.SphericalQuadraticBankDeterminantHolder
