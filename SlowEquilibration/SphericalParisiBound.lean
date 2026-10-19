-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConstrainedConcentration
public import SlowEquilibration.CSReplicaSymmetric

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- The actual finite-dimensional quenched spherical pressure. The size-zero
convention is inherited from real division; statements below use positive size. -/
def quenchedPressure (N : ℕ) (μ : FiniteMixture) (β : ℝ) : ℝ :=
  (∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
    ∂disorderLaw N μ.maxDegree) / (N : ℝ)

/-- Jensen's logarithm inequality, proved from the supporting line and ordinary
Bochner integrals. Both integrability requirements are explicit. -/
theorem integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : Integrable f ν) (hlog : Integrable (fun x => Real.log (f x)) ν)
    (hpos : ∀ᵐ x ∂ν, 0 < f x) :
    (∫ x, Real.log (f x) ∂ν) ≤ Real.log (∫ x, f x ∂ν) := by
  let a := ∫ x, f x ∂ν
  have hnonneg : 0 ≤ᵐ[ν] f := hpos.mono (fun _ hx => hx.le)
  have hs : ν (Function.support f) = 1 := by
    calc
      ν (Function.support f) = ν univ := measure_congr (by
        filter_upwards [hpos] with x hx
        exact propext ⟨fun _ => mem_univ x, fun _ => hx.ne'⟩)
      _ = 1 := measure_univ
  have ha : 0 < a := (integral_pos_iff_support_of_nonneg_ae hnonneg hf).mpr
    (by rw [hs]; exact zero_lt_one)
  have hi : Integrable (fun x => f x / a - 1) ν := (hf.div_const a).sub (integrable_const 1)
  have hineq : (∫ x, Real.log (f x) - Real.log a ∂ν) ≤
      ∫ x, f x / a - 1 ∂ν := by
    apply integral_mono_ae (hlog.sub (integrable_const _)) hi
    filter_upwards [hpos] with x hx
    change Real.log (f x) - Real.log a ≤ f x / a - 1
    rw [← Real.log_div hx.ne' ha.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [integral_sub hlog (integrable_const _), integral_sub (hf.div_const a)
    (integrable_const 1), integral_div, integral_const, integral_const] at hineq
  simp only [probReal_univ, smul_eq_mul, one_mul] at hineq
  change (∫ x, Real.log (f x) ∂ν) - Real.log a ≤ a / a - 1 at hineq
  rw [div_self ha.ne', sub_self] at hineq
  exact sub_nonpos.mp hineq

theorem mixture_logPartition_integrable {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
      (disorderLaw N μ.maxDegree) := by
  have hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1 := by
    rw [covariancePolynomial_mixture]
    exact μ.xi_pos (by norm_num)
  simpa only [mixturePartition, fieldOfMixture, partition, partitionAgainst] using
    logPartitionAgainst_disorder_integrable hN (sphereLaw N) (sphereLaw_support hN)
      (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hcov hβ

/-- The annealed upper bound on the literal quenched spherical pressure at
every finite positive dimension. This is the Dirac-zero CS trial value; it
does not assert the thermodynamic Parisi formula. -/
theorem quenchedPressure_le_annealed {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) :
    quenchedPressure N μ β ≤ β ^ 2 * μ.xi 1 / 2 := by
  have hpint : Integrable (mixturePartition (N := N) μ β) (disorderLaw N μ.maxDegree) :=
    field_exp_prod_integrable hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β |>.integral_prod_left
  have h := integral_log_le_log_integral (disorderLaw N μ.maxDegree) hpint
    (mixture_logPartition_integrable hN μ hβ)
    (Eventually.of_forall (mixturePartition_pos hN μ β))
  rw [mixture_expected_partition hN μ β, Real.log_exp] at h
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  unfold quenchedPressure
  apply (div_le_iff₀ hNr).mpr
  nlinarith

theorem quenchedPressure_le_diracZero_CS {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) :
    quenchedPressure N μ β ≤
      CrisantiSommers.functional β μ.xi (Measure.dirac (0 : ℝ)) 0 := by
  rw [CSReplicaSymmetric.functional_diracZero]
  exact quenchedPressure_le_annealed hN μ hβ

@[simp] theorem quenchedPressure_zero (N : ℕ) (μ : FiniteMixture) :
    quenchedPressure N μ 0 = 0 := by
  simp [quenchedPressure, mixturePartition, partition]

end
end SlowEquilibration.SphericalModel
