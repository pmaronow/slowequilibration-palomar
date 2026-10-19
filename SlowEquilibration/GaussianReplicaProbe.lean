-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaCalculus

@[expose] public section

/-! # Genuine Gaussian perturbation-energy replica response

The tested perturbation energy is a literal Gaussian field evaluated at one
of the independently sampled replicas. Its exact Gaussian IBP response is
proved for arbitrary bounded base spin laws. This is the finite-dimensional
IBP step preceding the Ghirlanda--Guerra self-averaging argument.
-/

namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators RealInnerProductSpace
open GaussianSpinInterpolation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- A fixed-coordinate bounded probe tested at one actual replica. -/
def probeObservable (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) {n : ℕ}
    (k : Fin n) (f : (Fin n → V) → ℝ) (i : ι) (σ : Fin n → V) : ℝ :=
  f σ*A (σ k) (EuclideanSpace.single i 1)

theorem probeObservable_measurable (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) {n : ℕ} (k : Fin n)
    (f : (Fin n → V) → ℝ) (hf : Measurable f) (i : ι) :
    Measurable (probeObservable A k f i) :=
  hf.mul (((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hA).comp
    (measurable_pi_apply k))

theorem probeObservable_bound (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) {KA C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA) {n : ℕ} (k : Fin n)
    (f : (Fin n → V) → ℝ) (hf : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (i : ι) :
    ∀ᵐ σ ∂replicaBase ν n, |probeObservable A k f i σ| ≤ C*KA := by
  have hk := (measurePreserving_eval (μ := fun _ : Fin n => ν) k).quasiMeasurePreserving.ae hA
  filter_upwards [hf,hk] with σ hf hA
  rw [probeObservable,abs_mul]
  apply mul_le_mul hf _ (abs_nonneg _) hC
  have he : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  have hh := (A (σ k)).le_opNorm (EuclideanSpace.single i 1) |>.trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  simpa only [Real.norm_eq_abs,he,mul_one] using hh

/-- The genuine tested Gaussian field at the selected replica. -/
def probeEnergy (ν : Measure V) (L A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {n : ℕ} (k : Fin n) (f : (Fin n → V) → ℝ) (w : EuclideanSpace ℝ ι) : ℝ :=
  replicaExpectation ν L n (fun σ => f σ*A (σ k) w) w

/-- The tested field decomposes into actual Gaussian coordinate responses. -/
theorem probeEnergy_eq_coordinate_sum (ν : Measure V) [IsProbabilityMeasure ν]
    (L A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L) (hAm : Measurable A)
    {K KA C : ℝ} (hK : 0 ≤ K) (_hKA : 0 ≤ KA) (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (hAb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA)
    {n : ℕ} (k : Fin n) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w : EuclideanSpace ℝ ι) :
    probeEnergy ν L A k f w = ∑ i, w i*replicaExpectation ν L n (probeObservable A k f i) w := by
  let G := Measure.pi (fun _ : Fin n => gibbsMeasure ν L w)
  let _ := gibbsMeasure_probability ν L hL hb w
  have hprob : IsProbabilityMeasure G := by dsimp [G]; infer_instance
  have hac : G ≪ replicaBase ν n := by
    rw [show G=gibbsMeasure (replicaBase ν n) (replicaLinear L n) w from
      (replica_gibbsMeasure_eq_pi ν L hL hK hb n w).symm]
    exact gibbsMeasure_absolutelyContinuous _ _ _
  have hi (i : ι) : Integrable (fun σ => w i*probeObservable A k f i σ) G := by
    apply Integrable.const_mul
    apply Integrable.of_bound (probeObservable_measurable A hAm k f hf i).aestronglyMeasurable (C*KA)
    exact ((probeObservable_bound ν A hC hAb k f hfb i).mono
      fun σ hσ => by simpa only [Real.norm_eq_abs] using hσ).filter_mono hac.ae_le
  have hw : (∑ i, w i • EuclideanSpace.single i 1) = w := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun ι ℝ).sum_repr w
  have heq : (fun σ : Fin n → V => f σ*A (σ k) w) =
      fun σ => ∑ i, w i*probeObservable A k f i σ := by
    funext σ
    nth_rw 1 [← hw]
    simp only [map_sum,map_smul,smul_eq_mul,probeObservable,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold probeEnergy replicaExpectation
  rw [heq,integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const_mul]
  rfl

theorem probe_coordinate_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L) (hAm : Measurable A)
    {K KA C : ℝ} (hK : 0 ≤ K) (hKA : 0 ≤ KA) (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (hAb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA)
    {n : ℕ} (k : Fin n) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (i : ι) :
    Integrable (fun w => w i*replicaExpectation ν L n (probeObservable A k f i) w)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hobs := probeObservable_measurable A hAm k f hf i
  have hbound := probeObservable_bound ν A hC hAb k f hfb i
  have hCK : 0 ≤ C*KA := mul_nonneg hC hKA
  have hcont : Continuous (fun w : EuclideanSpace ℝ ι =>
      w i*replicaExpectation ν L n (probeObservable A k f i) w) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).mul
      (replicaExpectation_contDiff ν L hL hK hCK hb n _ hobs hbound).continuous
  apply (gaussian_norm_integrable (ι := ι) |>.const_mul (C*KA)).mono' hcont.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [norm_mul]
    calc
      _ ≤ ‖w‖*(C*KA) := mul_le_mul (PiLp.norm_apply_le w i)
        (norm_replicaExpectation_le ν L hL hK hCK hb n _ hobs hbound w)
        (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring

/-- Exact actual perturbation-energy Gaussian integration by parts for
an arbitrary bounded observable of n independent Gibbs replicas. -/
theorem probeEnergy_gaussian_ibp (ν : Measure V) [IsProbabilityMeasure ν]
    (L A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L) (hAm : Measurable A)
    {K KA C : ℝ} (hK : 0 ≤ K) (hKA : 0 ≤ KA) (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (hAb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA)
    {n : ℕ} (k : Fin n) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) :
    (∫ w,probeEnergy ν L A k f w ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      ∑ i, ∫ w,
        replicaExpectation ν L n (fun σ => probeObservable A k f i σ*
          replicaLinear L n σ (EuclideanSpace.single i 1)) w -
        replicaExpectation ν L n (probeObservable A k f i) w*
          replicaExpectation ν L n (fun σ => replicaLinear L n σ (EuclideanSpace.single i 1)) w
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  simp_rw [probeEnergy_eq_coordinate_sum ν L A hL hAm hK hKA hC hb hAb k f hf hfb]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    probe_coordinate_gaussian_integrable ν L A hL hAm hK hKA hC hb hAb k f hf hfb i)]
  apply Finset.sum_congr rfl
  intro i _
  have h := replicaExpectation_gaussian_ibp ν L hL hK (mul_nonneg hC hKA) hb n
    (probeObservable A k f i) (probeObservable_measurable A hAm k f hf i)
    (probeObservable_bound ν A hC hAb k f hfb i) (EuclideanSpace.single i 1)
  simpa only [EuclideanSpace.inner_single_left,one_mul,conj_trivial] using h

end
end SlowEquilibration.GaussianReplicaCalculus
