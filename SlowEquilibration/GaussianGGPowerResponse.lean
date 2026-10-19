-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGPowerAlgebra

/-! The actual Gaussian selected-covariance response gives a normalized
power-GG error. The constant diagonal is proved by the model adapter;
its n=1 IBP score identity and n=m+1 old-neighbor algebra are derived
from ordinary finite-product Gibbs laws. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianReplicaCalculus

open MeasureTheory Set
open GaussianSpinInterpolation GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationDeviation GaussianPerturbationIntegrated
open scoped BigOperators RealInnerProductSpace

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- Actual constant-diagonal covariance GG estimate; the selected
Gaussian response and its mean score are both proved, not assumed. -/
theorem covarianceGG_le_selected_deviation (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀v,‖L v‖≤K) (label : ι → Bool)
    (x a : ℝ) (hxpos : 0<x) (hdiag : ∀z,selectedKernel L label z z=a)
    (m : ℕ) (f : (Fin (m+1) → V) → ℝ) (hf : Measurable f) (hfb : ∀σ,|f σ|≤1) :
    |covarianceGG ν (parameterLinear L label x) (selectedKernel L label) m f|≤
      (meanThermalDeviation ν L label x+energyFluctuation ν L label x)/(((m:ℝ)+1)*x) := by
  let Lx := parameterLinear L label x
  let B := (Fintype.card ι:ℝ)*K^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hx : ∀ᵐ v ∂ν,‖Lx v‖≤(1+|x|)*K := .of_forall (parameterLinear_pointwise_bound L label hK hb x)
  have hLx : Measurable Lx := parameterLinear_measurable L hL label x
  let row : (Fin (m+1) → V) → ℝ := fun σ => f σ*∑j,selectedKernel L label (σ 0) (σ j)
  let fresh : (Fin (m+2) → V) → ℝ := fun σ =>
    f (initialReplicas σ)*selectedKernel L label (σ 0) (σ (Fin.last (m+1)))
  have hrow : Measurable row := by
    have hk (j : Fin (m+1)) : Measurable (fun σ : Fin (m+1) → V => selectedKernel L label (σ 0) (σ j)) := by
      have hm : Measurable (fun σ : Fin (m+1) → V => (σ 0,σ j)) :=
        (measurable_pi_apply 0).prodMk (measurable_pi_apply j)
      simpa only [Function.comp_def] using (selectedKernel_joint_measurable L hL label).comp hm
    have hs := Finset.measurable_sum Finset.univ (fun j hj => hk j)
    simpa only [row,Function.comp_def] using measurable_mul.comp (hf.prodMk hs)
  have hrowb (σ : Fin (m+1) → V) : |row σ|≤((m:ℝ)+1)*B := by
    have hs : |∑j : Fin (m+1),selectedKernel L label (σ 0) (σ j)|≤((m:ℝ)+1)*B := by
      calc
        _ ≤ ∑j : Fin (m+1),|selectedKernel L label (σ 0) (σ j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑_j : Fin (m+1),B := Finset.sum_le_sum fun j hj => selectedKernel_abs_bound L hK hb label _ _
        _ = _ := by simp
    change |f σ*∑j,selectedKernel L label (σ 0) (σ j)|≤_
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hfb σ) hs (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hfresh : Measurable fresh := by
    have hm : Measurable (fun σ : Fin (m+2) → V => (σ 0,σ (Fin.last (m+1)))) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply (Fin.last (m+1)))
    have hk : Measurable (fun σ : Fin (m+2) → V => selectedKernel L label (σ 0) (σ (Fin.last (m+1)))) := by
      simpa only [Function.comp_def] using (selectedKernel_joint_measurable L hL label).comp hm
    simpa only [fresh,Function.comp_def] using measurable_mul.comp
      ((hf.comp (initialReplicas_measurable (m+1))).prodMk hk)
  have hfreshb (σ : Fin (m+2) → V) : |fresh σ|≤B := by
    change |f (initialReplicas σ)*selectedKernel L label (σ 0) (σ (Fin.last (m+1)))|≤_
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hfb (initialReplicas σ))
      (selectedKernel_abs_bound L hK hb label _ _) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hirow := replicaExpectation_gaussian_integrable ν Lx hLx (by positivity) (by positivity)
    hx (m+1) row hrow (.of_forall hrowb)
  have hifresh := replicaExpectation_gaussian_integrable ν Lx hLx (by positivity) hB
    hx (m+2) fresh hfresh (.of_forall hfreshb)
  have hbase := tested_selected_covariance_response_le ν L hL hK hb label x (0 : Fin (m+1)) f hf hfb
  have heqIntegral : (∫w,replicaExpectation ν Lx (m+1) row w-
      ((m+1:ℕ):ℝ)*replicaExpectation ν Lx (m+2) fresh w ∂SYK.standardGaussianMeasureOnEuclidean ι)=
      meanReplica ν Lx (m+1) row-((m+1:ℕ):ℝ)*meanReplica ν Lx (m+2) fresh := by
    rw [integral_sub hirow (hifresh.const_mul _),integral_const_mul]
    rfl
  change |x*(∫w,replicaExpectation ν Lx (m+1) row w-
      ((m+1:ℕ):ℝ)*replicaExpectation ν Lx (m+2) fresh w ∂SYK.standardGaussianMeasureOnEuclidean ι)-
      meanScore ν L label x*meanReplica ν Lx (m+1) f|≤_ at hbase
  rw [heqIntegral,meanScore_eq_selected_pair ν L hL hK hb label x a hdiag] at hbase
  have hrowMean := selected_row_mean_eq ν L hL hK hb label x a hdiag m f hf hfb
  change meanReplica ν Lx (m+1) row=_ at hrowMean
  rw [hrowMean] at hbase
  have hn : 0<(m:ℝ)+1 := by positivity
  have heq : x*(a*meanReplica ν Lx (m+1) f+
      (∑j : Fin m,meanReplica ν Lx (m+1) (fun σ => f σ*selectedKernel L label (σ 0) (σ j.succ)))-
      ((m+1:ℕ):ℝ)*meanReplica ν Lx (m+2) fresh)-
      (x*(a-meanReplica ν Lx 2 (fun σ => selectedKernel L label (σ 0) (σ 1))))*
        meanReplica ν Lx (m+1) f=
      -(((m:ℝ)+1)*x)*covarianceGG ν Lx (selectedKernel L label) m f := by
    unfold covarianceGG
    change x*(a*meanReplica ν Lx (m+1) f+
      (∑j : Fin m,meanReplica ν Lx (m+1) (fun σ => f σ*selectedKernel L label (σ 0) (σ j.succ)))-
      ((m+1:ℕ):ℝ)*meanReplica ν Lx (m+2) fresh)-
      (x*(a-meanReplica ν Lx 2 (fun σ => selectedKernel L label (σ 0) (σ 1))))*
        meanReplica ν Lx (m+1) f=
      -(((m:ℝ)+1)*x)*(meanReplica ν Lx (m+2) fresh-
        meanReplica ν Lx (m+1) f*meanReplica ν Lx 2 (fun σ => selectedKernel L label (σ 0) (σ 1))/((m:ℝ)+1)-
        (∑j : Fin m,meanReplica ν Lx (m+1) (fun σ => f σ*selectedKernel L label (σ 0) (σ j.succ)))/((m:ℝ)+1))
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp [hn.ne']
    ring
  rw [heq,abs_mul,abs_neg,abs_of_pos (mul_pos hn hxpos)] at hbase
  exact (le_div_iff₀ (mul_pos hn hxpos)).mpr (by simpa only [mul_comm] using hbase)

/-- The actual selected covariance a R^p gives the original tested-power
GG discrepancy, with exact positive normalization n*x*a. -/
theorem powerGG_le_selected_deviation (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀v,‖L v‖≤K) (label : ι → Bool)
    (R : V → V → ℝ) (p : ℕ) (a x : ℝ) (ha : 0<a) (hx : 0<x)
    (hcov : ∀z y,selectedKernel L label z y=a*(R z y)^p) (hRdiag : ∀z,R z z=1)
    (m : ℕ) (f : (Fin (m+1) → V) → ℝ) (hf : Measurable f) (hfb : ∀σ,|f σ|≤1) :
    |powerGG ν (parameterLinear L label x) R m p f|≤
      (meanThermalDeviation ν L label x+energyFluctuation ν L label x)/(((m:ℝ)+1)*x*a) := by
  have hdiag (z) : selectedKernel L label z z=a := by rw [hcov,hRdiag];simp
  have hbase := covarianceGG_le_selected_deviation ν L hL hK hb label x a hx hdiag m f hf hfb
  have hc : selectedKernel L label=(fun z y => a*(R z y)^p) := funext fun z => funext (hcov z)
  rw [hc,covarianceGG_const_mul,abs_mul,abs_of_pos ha] at hbase
  have hn : 0<(m:ℝ)+1 := by positivity
  have ht := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hbase)
  change |powerGG ν (parameterLinear L label x) R m p f|≤_
  exact ht.trans_eq (by rw [div_div];congr 1;ring)

end SlowEquilibration.GaussianReplicaCalculus
