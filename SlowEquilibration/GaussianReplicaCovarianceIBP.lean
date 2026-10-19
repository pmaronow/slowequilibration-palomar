-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaProbe
public import SlowEquilibration.GaussianReplicaExtension

@[expose] public section

/-! Exact tested-field Gaussian IBP expressed in genuine replica covariance
kernels, including the fresh replica from the actual product Gibbs law. -/
namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
open GaussianSpinInterpolation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def crossKernel (A L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (z y : V) : ℝ :=
  ∑ i,A z (EuclideanSpace.single i 1)*L y (EuclideanSpace.single i 1)

private theorem coordinate_norm_bound (A : EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hA : ‖A‖ ≤ K) (i : ι) :
    |A (EuclideanSpace.single i 1)| ≤ K := by
  have h:=A.le_opNorm (EuclideanSpace.single i (1:ℝ))
  simpa only [Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one] using
    h.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

theorem probeEnergy_covariance_ibp (ν : Measure V) [IsProbabilityMeasure ν]
    (L A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L) (hA : Measurable A)
    {K KA C : ℝ} (hK : 0 ≤ K) (hKA : 0 ≤ KA) (hC : 0 ≤ C)
    (hb : ∀ v,‖L v‖ ≤ K) (hAb : ∀ v,‖A v‖ ≤ KA)
    {n : ℕ} (k : Fin n) (f : (Fin n → V) → ℝ)
    (hf : Measurable f) (hfb : ∀ σ,|f σ| ≤ C) :
    (∫ w,probeEnergy ν L A k f w ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      ∫ w,
        replicaExpectation ν L n (fun σ => f σ*∑ j,crossKernel A L (σ k) (σ j)) w-
          (n:ℝ)*replicaExpectation ν L (n+1)
            (fun σ => f (initialReplicas σ)*crossKernel A L (σ k.castSucc) (σ (Fin.last n))) w
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let old := fun i : ι => fun σ : Fin n → V =>
    probeObservable A k f i σ*replicaLinear L n σ (EuclideanSpace.single i 1)
  let fresh := fun i : ι => fun σ : Fin (n+1) → V =>
    probeObservable A k f i (initialReplicas σ)*L (σ (Fin.last n)) (EuclideanSpace.single i 1)
  have hb' : ∀ᵐ v ∂ν,‖L v‖ ≤ K := .of_forall hb
  have hAb' : ∀ᵐ v ∂ν,‖A v‖ ≤ KA := .of_forall hAb
  have hfb' : ∀ᵐ σ ∂replicaBase ν n,|f σ| ≤ C := .of_forall hfb
  have hprobe (i : ι) : ∀ σ : Fin n → V,|probeObservable A k f i σ| ≤ C*KA := by
    intro σ
    rw [probeObservable,abs_mul]
    exact mul_le_mul (hfb σ) (coordinate_norm_bound _ (hAb _) i) (abs_nonneg _) hC
  have hlin (i : ι) : ∀ σ : Fin n → V,
      |replicaLinear L n σ (EuclideanSpace.single i 1)| ≤ (n:ℝ)*K := by
    intro σ
    simp only [replicaLinear,sum_apply]
    calc
      _ ≤ ∑ j : Fin n,|L (σ j) (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n,K := Finset.sum_le_sum (fun j _ => coordinate_norm_bound _ (hb _) i)
      _ = _ := by simp
  have hOld (i : ι) : Measurable (old i) :=
    (probeObservable_measurable A hA k f hf i).mul
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp
        (replicaLinear_measurable L hL n))
  have hFresh (i : ι) : Measurable (fresh i) :=
    ((probeObservable_measurable A hA k f hf i).comp (initialReplicas_measurable n)).mul
      (((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hL).comp
        (measurable_pi_apply (Fin.last n)))
  have hbOld (i : ι) : ∀ σ,|old i σ| ≤ C*KA*((n:ℝ)*K) := by
    intro σ
    change |probeObservable A k f i σ*replicaLinear L n σ (EuclideanSpace.single i 1)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hprobe i σ) (hlin i σ) (abs_nonneg _) (mul_nonneg hC hKA)
  have hbFresh (i : ι) : ∀ σ,|fresh i σ| ≤ C*KA*K := by
    intro σ
    change |probeObservable A k f i (initialReplicas σ)*L (σ (Fin.last n)) (EuclideanSpace.single i 1)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hprobe i _) (coordinate_norm_bound _ (hb _) i)
      (abs_nonneg _) (mul_nonneg hC hKA)
  have hProduct (i : ι) (w : EuclideanSpace ℝ ι) :
      replicaExpectation ν L n (probeObservable A k f i) w*
        replicaExpectation ν L n (fun σ => replicaLinear L n σ (EuclideanSpace.single i 1)) w =
      (n:ℝ)*replicaExpectation ν L (n+1) (fresh i) w := by
    rw [replicaExpectation_linear_apply ν L hL hb' n w]
    rw [show replicaExpectation ν L (n+1) (fresh i) w=
        replicaExpectation ν L n (probeObservable A k f i) w*
          expectation ν (fun z => L z (EuclideanSpace.single i 1)) L w from
      replicaExpectation_append ν L hL hb' n w (probeObservable A k f i)
        (fun z => L z (EuclideanSpace.single i 1))]
    ring
  have hi (i : ι) : Integrable (fun w => replicaExpectation ν L n (old i) w-
      replicaExpectation ν L n (probeObservable A k f i) w*
        replicaExpectation ν L n (fun σ => replicaLinear L n σ (EuclideanSpace.single i 1)) w)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    have hio := replicaExpectation_gaussian_integrable ν L hL hK
      (by positivity : 0 ≤ C*KA*((n:ℝ)*K)) hb' n _ (hOld i) (.of_forall (hbOld i))
    have hif := (replicaExpectation_gaussian_integrable ν L hL hK
      (by positivity : 0 ≤ C*KA*K) hb' (n+1) _ (hFresh i) (.of_forall (hbFresh i))).const_mul (n:ℝ)
    apply hio.sub
    exact hif.congr (.of_forall fun w => (hProduct i w).symm)
  have hOldSum (w : EuclideanSpace ℝ ι) :
      (∑ i,replicaExpectation ν L n (old i) w)=
        replicaExpectation ν L n (fun σ => f σ*∑ j,crossKernel A L (σ k) (σ j)) w := by
    rw [← replicaExpectation_finiteSum ν L hL hK hb' n old hOld
      (fun i => .of_forall (hbOld i)) w]
    congr 1
    funext σ
    simp only [old,probeObservable,replicaLinear,sum_apply,Finset.mul_sum,crossKernel]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hFreshSum (w : EuclideanSpace ℝ ι) :
      (∑ i,replicaExpectation ν L (n+1) (fresh i) w)=
        replicaExpectation ν L (n+1)
          (fun σ => f (initialReplicas σ)*crossKernel A L (σ k.castSucc) (σ (Fin.last n))) w := by
    rw [← replicaExpectation_finiteSum ν L hL hK hb' (n+1) fresh hFresh
      (fun i => .of_forall (hbFresh i)) w]
    congr 1
    funext σ
    simp only [fresh,probeObservable,initialReplicas,crossKernel,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [probeEnergy_gaussian_ibp ν L A hL hA hK hKA hC hb' hAb' k f hf hfb',
    ← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  exact .of_forall fun w => by
    simp_rw [hProduct]
    rw [Finset.sum_sub_distrib,hOldSum,← Finset.mul_sum,hFreshSum]

end
end SlowEquilibration.GaussianReplicaCalculus
