-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSelectedReplicaIBP
public import SlowEquilibration.GaussianPerturbationDeviation

@[expose] public section

/-! A bounded true replica test times the selected energy has a Gaussian
centered expectation bounded by the actual thermal and quenched deviations. -/
namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
open GaussianSpinInterpolation GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationIntegrated GaussianPerturbationDeviation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem selected_tested_energy_pointwise_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v,‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) {n : ℕ} (k : Fin n)
    (f : (Fin n → V) → ℝ) (hf : Measurable f) (hfb : ∀ σ,|f σ| ≤ 1)
    (w : EuclideanSpace ℝ ι) :
    |probeEnergy ν (parameterLinear L label x) (selectedLinear L label) k f w-
      parameterScore ν L label w x*replicaExpectation ν (parameterLinear L label x) n f w| ≤
      thermalDeviation ν L label w x := by
  let G:=gibbsMeasure ν L (parameterOperator label x w)
  let R:=Measure.pi (fun _ : Fin n => G)
  let ρ:=fun z => L z (GaussianSpinComparison.coordinateMask label true w)
  let c:=parameterScore ν L label w x
  have hb' : ∀ᵐ v ∂ν,‖L v‖ ≤ K := .of_forall hb
  let _ : IsProbabilityMeasure G:=gibbsMeasure_probability ν L hL hb' _
  have hρ : Measurable ρ:=
    (ContinuousLinearMap.apply ℝ ℝ (GaussianSpinComparison.coordinateMask label true w)).continuous.measurable.comp hL
  have hρb (v : V) : |ρ v| ≤ K*‖w‖ := by
    exact ((L v).le_opNorm _).trans
      (mul_le_mul (hb v) (GaussianPerturbationParameter.coordinateMask_norm_le label true w)
        (norm_nonneg _) hK)
  have hiρ : Integrable (fun σ : Fin n → V => ρ (σ k)) R := by
    apply Integrable.of_bound (hρ.comp (measurable_pi_apply k)).aestronglyMeasurable (K*‖w‖)
    exact .of_forall fun σ => by
      change |ρ (σ k)| ≤ _
      exact hρb (σ k)
  have hif : Integrable f R := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact .of_forall fun σ => by simpa only [Real.norm_eq_abs] using hfb σ
  have hifρ : Integrable (fun σ : Fin n → V => f σ*ρ (σ k)) R := by
    apply Integrable.of_bound (hf.mul (hρ.comp (measurable_pi_apply k))).aestronglyMeasurable (K*‖w‖)
    exact .of_forall fun σ => by
      change |f σ*ρ (σ k)| ≤ _
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (hfb σ) (hρb (σ k)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hiδ : Integrable (fun σ : Fin n → V => |ρ (σ k)-c|) R :=
    (hiρ.sub (integrable_const c)).abs
  have hiweighted : Integrable (fun σ : Fin n → V => f σ*(ρ (σ k)-c)) R := by
    apply (hifρ.sub (hif.mul_const c)).congr
    exact .of_forall fun σ => by
      change f σ*ρ (σ k)-f σ*c=f σ*(ρ (σ k)-c)
      ring
  have heq : probeEnergy ν (parameterLinear L label x) (selectedLinear L label) k f w-
      parameterScore ν L label w x*replicaExpectation ν (parameterLinear L label x) n f w =
      ∫ σ,f σ*(ρ (σ k)-c) ∂R := by
    change (∫ σ,f σ*ρ (σ k) ∂R)-c*(∫ σ,f σ ∂R)=_
    simp_rw [mul_sub]
    rw [integral_sub hifρ (hif.mul_const c),integral_mul_const]
    ring
  rw [heq]
  calc
    _ ≤ ∫ σ,|f σ*(ρ (σ k)-c)| ∂R := abs_integral_le_integral_abs
    _ ≤ ∫ σ,|ρ (σ k)-c| ∂R := integral_mono hiweighted.abs hiδ (fun σ => by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hfb σ) (abs_nonneg _))
    _ = ∫ z,|ρ z-c| ∂G := integral_comp_eval
      (μ := fun _ : Fin n => G) (i:=k)
      (continuous_abs.measurable.comp (hρ.sub_const c)).aestronglyMeasurable
    _ = _ := rfl

theorem selected_tested_energy_centered_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v,‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) {n : ℕ} (k : Fin n)
    (f : (Fin n → V) → ℝ) (hf : Measurable f) (hfb : ∀ σ,|f σ| ≤ 1) :
    |(∫ w,probeEnergy ν (parameterLinear L label x) (selectedLinear L label) k f w
        ∂SYK.standardGaussianMeasureOnEuclidean ι)-
      meanScore ν L label x*(∫ w,replicaExpectation ν (parameterLinear L label x) n f w
        ∂SYK.standardGaussianMeasureOnEuclidean ι)| ≤
      meanThermalDeviation ν L label x+energyFluctuation ν L label x := by
  let Lx:=parameterLinear L label x
  let A:=selectedLinear L label
  let P:=probeEnergy ν Lx A k f
  let F:=replicaExpectation ν Lx n f
  let c:=meanScore ν L label x
  let d:=SYK.standardGaussianMeasureOnEuclidean ι
  have hb' : ∀ᵐ v ∂ν,‖L v‖ ≤ K := .of_forall hb
  have hx : ∀ᵐ v ∂ν,‖Lx v‖ ≤ (1+|x|)*K:=.of_forall (parameterLinear_pointwise_bound L label hK hb x)
  have hA : Measurable A:=selectedLinear_measurable L hL label
  have hAb : ∀ᵐ v ∂ν,‖A v‖ ≤ K:=.of_forall (selectedLinear_bound L label hK hb)
  have hLx : Measurable Lx:=parameterLinear_measurable L hL label x
  have hif : Integrable F d:=replicaExpectation_gaussian_integrable ν Lx hLx
    (by positivity) (by norm_num) hx n f hf (.of_forall hfb)
  have hip : Integrable P d := by
    have heq := fun w => probeEnergy_eq_coordinate_sum ν Lx A hLx hA
      (by positivity) hK (by norm_num) hx hAb k f hf (.of_forall hfb) w
    rw [show P=(fun w => ∑ i,w i*replicaExpectation ν Lx n (probeObservable A k f i) w)
      from funext heq]
    exact integrable_finsetSum Finset.univ fun i _ => probe_coordinate_gaussian_integrable
      ν Lx A hLx hA (by positivity) hK (by norm_num) hx hAb k f hf (.of_forall hfb) i
  have hpoint (w) : |P w-c*F w| ≤ thermalDeviation ν L label w x+
      |parameterScore ν L label w x-c| := by
    have hbase:=selected_tested_energy_pointwise_le ν L hL hK hb label x k f hf hfb w
    have hF : |F w| ≤ 1:=by
      simpa only [Real.norm_eq_abs] using norm_replicaExpectation_le ν Lx hLx
        (by positivity) (by norm_num) hx n f hf (.of_forall hfb) w
    have hsplit : P w-c*F w=(P w-parameterScore ν L label w x*F w)+
        (parameterScore ν L label w x-c)*F w := by ring
    rw [hsplit]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add hbase (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hF (abs_nonneg _))
  have hidev : Integrable (fun w => |parameterScore ν L label w x-c|) d :=
    ((parameterScore_gaussian_integrable ν L hL hK hb' label x).sub (integrable_const c)).abs
  have hith : Integrable (fun w => thermalDeviation ν L label w x) d:=
    thermalDeviation_gaussian_integrable ν L hL hK hb' label x
  rw [show (∫ w,P w ∂d)-c*(∫ w,F w ∂d)=∫ w,P w-c*F w ∂d from
    (by rw [integral_sub hip (hif.const_mul c),integral_const_mul])]
  calc
    _ ≤ ∫ w,|P w-c*F w| ∂d := abs_integral_le_integral_abs
    _ ≤ ∫ w,thermalDeviation ν L label w x+|parameterScore ν L label w x-c| ∂d :=
      integral_mono (hip.sub (hif.const_mul c)).abs (hith.add hidev) hpoint
    _ = _ := by rw [integral_add hith hidev];rfl

end
end SlowEquilibration.GaussianReplicaCalculus
