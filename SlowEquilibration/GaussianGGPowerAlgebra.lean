-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGResponse
public import SlowEquilibration.GaussianGGEnsemble

/-! Ordinary diagonal and old-neighbor algebra for genuine Gaussian
Gibbs replicas. The single-replica selected IBP identity identifies the
actual mean score. The finite old-neighbor sum contains the literal
constant diagonal, rather than an assumed GG normalization. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianReplicaCalculus

open MeasureTheory Set
open GaussianSpinInterpolation GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationDeviation
open scoped BigOperators RealInnerProductSpace

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- Literal Gaussian mean of the actual finite-product Gibbs expectation. -/
def meanReplica (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (n : ℕ) (f : (Fin n → V) → ℝ) : ℝ :=
  ∫w,replicaExpectation ν L n f w ∂SYK.standardGaussianMeasureOnEuclidean ι

def covarianceGG (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (A : V → V → ℝ) (m : ℕ) (f : (Fin (m+1) → V) → ℝ) : ℝ :=
  meanReplica ν L (m+2) (fun σ => f (initialReplicas σ)*A (σ 0) (σ (Fin.last (m+1))))-
    meanReplica ν L (m+1) f*meanReplica ν L 2 (fun σ => A (σ 0) (σ 1))/((m:ℝ)+1)-
    (∑j : Fin m,meanReplica ν L (m+1) (fun σ => f σ*A (σ 0) (σ j.succ)))/((m:ℝ)+1)

def powerGG (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (R : V → V → ℝ) (m p : ℕ) (f : (Fin (m+1) → V) → ℝ) : ℝ :=
  covarianceGG ν L (fun z y => (R z y)^p) m f

omit [DecidableEq ι] in
theorem meanReplica_const_mul (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (n : ℕ) (f : (Fin n → V) → ℝ) (a : ℝ) :
    meanReplica ν L n (fun σ => a*f σ)=a*meanReplica ν L n f := by
  unfold meanReplica replicaExpectation
  simp_rw [integral_const_mul]

omit [DecidableEq ι] in
theorem covarianceGG_const_mul (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (A : V → V → ℝ) (m : ℕ) (f : (Fin (m+1) → V) → ℝ) (a : ℝ) :
    covarianceGG ν L (fun z y => a*A z y) m f=a*covarianceGG ν L A m f := by
  have hfresh : (fun σ : Fin (m+2) → V => f (initialReplicas σ)*(a*A (σ 0) (σ (Fin.last (m+1)))))=
      fun σ => a*(f (initialReplicas σ)*A (σ 0) (σ (Fin.last (m+1)))) := by funext σ;ring
  have hold (j : Fin m) : (fun σ : Fin (m+1) → V => f σ*(a*A (σ 0) (σ j.succ)))=
      fun σ => a*(f σ*A (σ 0) (σ j.succ)) := by funext σ;ring
  unfold covarianceGG
  rw [hfresh,meanReplica_const_mul,meanReplica_const_mul]
  simp_rw [hold,meanReplica_const_mul]
  rw [← Finset.mul_sum]
  ring

 theorem selectedKernel_joint_measurable
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L) (label : ι → Bool) :
    Measurable (fun z : V × V => selectedKernel L label z.1 z.2) := by
  unfold selectedKernel
  apply Finset.measurable_sum
  intro i hi
  have hc : Measurable (fun z : V => L z (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hL
  by_cases h : label i=true
  · simp only [h,ite_true]
    exact (hc.comp measurable_fst).mul (hc.comp measurable_snd)
  · simp only [h]
    exact measurable_const

omit [MeasurableSpace V] in
theorem selectedKernel_abs_bound
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) {K : ℝ} (hK : 0≤K)
    (hb : ∀ v,‖L v‖≤K) (label : ι → Bool) (z y : V) :
    |selectedKernel L label z y|≤(Fintype.card ι:ℝ)*K^2 := by
  have hc (v : V) (i : ι) : |L v (EuclideanSpace.single i 1)|≤K := by
    simpa only [Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one] using
      ((L v).le_opNorm (EuclideanSpace.single i 1)).trans
        (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _))
  unfold selectedKernel
  calc
    _ ≤ ∑i, |if label i=true then L z (EuclideanSpace.single i 1)*L y (EuclideanSpace.single i 1) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i : ι,K^2 := Finset.sum_le_sum fun i hi => by
      split_ifs
      · rw [abs_mul,pow_two]
        exact mul_le_mul (hc z i) (hc y i) (abs_nonneg _) hK
      · simp only [abs_zero]
        exact sq_nonneg _
    _ = _ := by simp

 theorem probeEnergy_one_eq_parameterScore (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ v,‖L v‖≤K) (label : ι → Bool) (x : ℝ)
    (w : EuclideanSpace ℝ ι) :
    probeEnergy ν (parameterLinear L label x) (selectedLinear L label) (0 : Fin 1) (fun _ => 1) w=
      parameterScore ν L label w x := by
  have hb' : ∀ᵐ v ∂ν,‖L v‖≤K := .of_forall hb
  have hx := parameterLinear_bound ν L hK hb' label x
  have hm : Measurable (fun z => selectedLinear L label z w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp (selectedLinear_measurable L hL label)
  rw [probeEnergy]
  simp only [one_mul]
  rw [replicaExpectation_coordinate ν _ (parameterLinear_measurable L hL label x) hx 1 0 w _ hm]
  rw [parameterScore,score_apply ν L hL hb']
  rfl

/-- The true n=1 selected Gaussian response identifies the score mean. -/
theorem meanScore_eq_selected_pair (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ v,‖L v‖≤K)
    (label : ι → Bool) (x a : ℝ) (hdiag : ∀z,selectedKernel L label z z=a) :
    meanScore ν L label x=x*(a-meanReplica ν (parameterLinear L label x) 2
      (fun σ => selectedKernel L label (σ 0) (σ 1))) := by
  let Lx := parameterLinear L label x
  let B := (Fintype.card ι:ℝ)*K^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hx : ∀ᵐ v ∂ν,‖Lx v‖≤(1+|x|)*K := .of_forall (parameterLinear_pointwise_bound L label hK hb x)
  have hLx : Measurable Lx := parameterLinear_measurable L hL label x
  have hpair : Measurable (fun σ : Fin 2 → V => selectedKernel L label (σ 0) (σ 1)) := by
    have hm : Measurable (fun σ : Fin 2 → V => (σ 0,σ 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    simpa only [Function.comp_def] using (selectedKernel_joint_measurable L hL label).comp hm
  have hpb : ∀σ : Fin 2 → V, |selectedKernel L label (σ 0) (σ 1)|≤B :=
    fun σ => selectedKernel_abs_bound L hK hb label _ _
  have hipair := replicaExpectation_gaussian_integrable ν Lx hLx (by positivity) hB hx 2 _ hpair (.of_forall hpb)
  have hpoint (w) : replicaExpectation ν Lx 1
      (fun σ => (1:ℝ)*∑j : Fin 1,selectedKernel L label (σ 0) (σ j)) w=a := by
    let _ := gibbsMeasure_probability ν Lx hLx hx w
    simp only [one_mul,Fin.sum_univ_one,hdiag,replicaExpectation,integral_const,
      probReal_univ,smul_eq_mul,one_mul]
  have hIBP := selected_probeEnergy_ibp ν L hL hK (C := 1) (by norm_num) hb label x (0 : Fin 1)
    (fun _ => 1) measurable_const (fun _ => by norm_num)
  simp_rw [probeEnergy_one_eq_parameterScore ν L hL hK hb] at hIBP
  change meanScore ν L label x=_ at hIBP
  have heq : (fun w => replicaExpectation ν Lx 1
        (fun σ => (1:ℝ)*∑j : Fin 1,selectedKernel L label (σ 0) (σ j)) w-
        (1:ℝ)*replicaExpectation ν Lx 2
          (fun σ => (1:ℝ)*selectedKernel L label (σ (0 : Fin 1).castSucc) (σ (Fin.last 1))) w)=
      fun w => a-replicaExpectation ν Lx 2 (fun σ => selectedKernel L label (σ 0) (σ 1)) w := by
    funext w
    rw [hpoint w]
    simp only [one_mul]
    rfl
  simp only [Nat.cast_one] at hIBP
  change meanScore ν L label x=x*(∫w, _ ∂SYK.standardGaussianMeasureOnEuclidean ι) at hIBP
  rw [heq,integral_sub (integrable_const a) hipair] at hIBP
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,meanReplica,Lx] using hIBP

/-- The ordinary Gaussian mean of the full covariance row contains its
true constant diagonal and the actual old-neighbor expectations. -/
theorem selected_row_mean_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀v,‖L v‖≤K) (label : ι → Bool) (x a : ℝ)
    (hdiag : ∀z,selectedKernel L label z z=a) (m : ℕ)
    (f : (Fin (m+1) → V) → ℝ) (hf : Measurable f) (hfb : ∀σ,|f σ|≤1) :
    meanReplica ν (parameterLinear L label x) (m+1)
      (fun σ => f σ*∑j : Fin (m+1),selectedKernel L label (σ 0) (σ j))=
      a*meanReplica ν (parameterLinear L label x) (m+1) f+
      ∑j : Fin m,meanReplica ν (parameterLinear L label x) (m+1)
        (fun σ => f σ*selectedKernel L label (σ 0) (σ j.succ)) := by
  let Lx := parameterLinear L label x
  let B := (Fintype.card ι:ℝ)*K^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hx : ∀ᵐ v ∂ν,‖Lx v‖≤(1+|x|)*K := .of_forall (parameterLinear_pointwise_bound L label hK hb x)
  have hLx : Measurable Lx := parameterLinear_measurable L hL label x
  let old (j : Fin m) (σ : Fin (m+1) → V) := f σ*selectedKernel L label (σ 0) (σ j.succ)
  have hmold (j : Fin m) : Measurable (old j) := by
    have hm : Measurable (fun σ : Fin (m+1) → V => (σ 0,σ j.succ)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply j.succ)
    have hk : Measurable (fun σ : Fin (m+1) → V => selectedKernel L label (σ 0) (σ j.succ)) := by
      simpa only [Function.comp_def] using (selectedKernel_joint_measurable L hL label).comp hm
    simpa only [old,Function.comp_def] using measurable_mul.comp (hf.prodMk hk)
  have hbold (j : Fin m) (σ : Fin (m+1) → V) : |old j σ|≤B := by
    change |f σ*selectedKernel L label (σ 0) (σ j.succ)|≤B
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hfb σ) (selectedKernel_abs_bound L hK hb label _ _)
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hiold (j : Fin m) := replicaExpectation_gaussian_integrable ν Lx hLx
    (by positivity) hB hx (m+1) (old j) (hmold j) (.of_forall (hbold j))
  have hif := replicaExpectation_gaussian_integrable ν Lx hLx
    (by positivity) (by norm_num) hx (m+1) f hf (.of_forall hfb)
  have hpoint (w : EuclideanSpace ℝ ι) : replicaExpectation ν Lx (m+1)
      (fun σ => f σ*∑j : Fin (m+1),selectedKernel L label (σ 0) (σ j)) w=
      a*replicaExpectation ν Lx (m+1) f w+∑j : Fin m,replicaExpectation ν Lx (m+1) (old j) w := by
    let _ := gibbsMeasure_probability ν Lx hLx hx w
    let R := Measure.pi (fun _ : Fin (m+1) => gibbsMeasure ν Lx w)
    have hfI : Integrable f R := Integrable.of_bound hf.aestronglyMeasurable 1
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using hfb σ)
    have hoI (j : Fin m) : Integrable (old j) R := Integrable.of_bound (hmold j).aestronglyMeasurable B
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using hbold j σ)
    unfold replicaExpectation
    simp_rw [Fin.sum_univ_succ,hdiag,mul_add,Finset.mul_sum]
    rw [integral_add (hfI.mul_const a) (integrable_finsetSum _ (fun j hj => hoI j)),
      integral_mul_const,integral_finsetSum _ (fun j hj => hoI j)]
    ring
  unfold meanReplica
  rw [show (fun w => replicaExpectation ν (parameterLinear L label x) (m+1)
    (fun σ => f σ*∑j : Fin (m+1),selectedKernel L label (σ 0) (σ j)) w)=
      (fun w => a*replicaExpectation ν Lx (m+1) f w+
        ∑j : Fin m,replicaExpectation ν Lx (m+1) (old j) w) from funext hpoint]
  rw [integral_add (hif.const_mul a) (integrable_finsetSum _ (fun j hj => hiold j)),
    integral_const_mul,integral_finsetSum _ (fun j hj => hiold j)]

end SlowEquilibration.GaussianReplicaCalculus
