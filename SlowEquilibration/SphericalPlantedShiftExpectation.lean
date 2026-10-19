-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedShift

@[expose] public section

/-! # Literal bounded expectations under the actual planted disorder shift -/
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory Set
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem planted_joint_expectation_eq_shift {N P : ℕ} (hN : 1≤N)
    (c : Degree P → ℝ) (hc : ∀ p,0≤c p) (β : ℝ)
    (F : Disorder N P × Vector N → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ z,|F z|≤C) :
    (∫ z,F z ∂plantedLaw c β)=
      ∫ x,∫ D : Disorder N P,F (D+plantedShift c β x,x) ∂disorderLaw N P ∂sphereLaw N := by
  have hint : Integrable (fun z : Disorder N P × Vector N => plantedDensity c β z*F z)
      ((disorderLaw N P).prod (sphereLaw N)) :=
    (plantedDensity_integrable hN c hc β).mul_bdd hF.aestronglyMeasurable
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  rw [plantedLaw,integral_withDensity_eq_integral_toReal_smul
    (plantedDensity_continuous c β).measurable.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpos (z : Disorder N P × Vector N) : 0≤plantedDensity c β z := (Real.exp_pos _).le
  simp_rw [ENNReal.toReal_ofReal (hpos _),smul_eq_mul]
  rw [integral_prod_symm _ hint]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have he := planted_disorder_shift_integral hN c hc β x hx
    (fun D => F (D,x)) (hF.comp (measurable_id.prodMk measurable_const))
  simpa only [mul_comm] using he

end
end SlowEquilibration.SphericalModel
