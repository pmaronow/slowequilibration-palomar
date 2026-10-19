-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFeature

@[expose] public section

/-! # Exact degree-one and degree-two physical source probe covariance -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel GaussianReplicaCalculus
open scoped Topology BigOperators InnerProductSpace
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The source probe is an actual supported transverse bank index; both
transverse degrees exist for every original physical degree at least two. -/
def amplitudeProbeIndex (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) (k : Fin 2) : BankIndex μ :=
  ⟨p₀,⟨k.val+1,by have hk := k.isLt; have hp := p₀.property; omega⟩⟩

lemma amplitudeProbe_condition_iff (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (i : BankIndex μ) :
    (i.1=p₀ ∧ i.2.val=k.val+1) ↔ i=amplitudeProbeIndex μ p₀ k := by
  rcases i with ⟨p,j⟩
  constructor
  · rintro ⟨hp,hj⟩
    change p=p₀ at hp
    change j.val=k.val+1 at hj
    subst p
    exact congrArg (Sigma.mk p₀) (Fin.ext hj)
  · intro hi
    cases hi
    exact ⟨rfl,rfl⟩

/-- Every exact selected-coordinate observable is the actual tensor feature. -/
theorem amplitudeBankLinear_single (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) (j : BankCoordinate n μ) :
    amplitudeBankLinear μ β x e p₀ s u (EuclideanSpace.single j 1)=
      β*(amplitudeBankFeature μ x e p₀ s u) j := by
  rw [amplitudeBankLinear,smul_apply,innerSL_apply_apply,EuclideanSpace.inner_single_right]
  simp only [smul_eq_mul,conj_trivial,one_mul]

/-- The selected Gaussian coordinate kernel is exactly the physical probe
kernel on the entire ambient spin space, before every probabilistic argument. -/
theorem selectedKernel_amplitudeBankLinear_eq (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (u v : Vector (n+1)) :
    selectedKernel (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) u v=
      β^2*bankComponentKernel μ x e (amplitudeProbeIndex μ p₀ k) u v := by
  unfold selectedKernel
  simp only [amplitudeBankLinear_single,amplitudeBankFeature,bankAmplitude_one,one_mul,
    amplitudeBankLabel,decide_eq_true_eq]
  rw [Fintype.sum_sigma]
  have he : (∑ i : BankIndex μ, ∑ I : SphericalAging.FiniteModel.TensorIndex n i.2.val,
      if i.1=p₀ ∧ i.2.val=k.val+1 then
        (β*(bankComponentScale μ x i u*SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u) I))*
        (β*(bankComponentScale μ x i v*SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint v) I)) else 0)=
      ∑ i : BankIndex μ, if i.1=p₀ ∧ i.2.val=k.val+1 then β^2*bankComponentKernel μ x e i u v else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1=p₀ ∧ i.2.val=k.val+1
    · simp [hi]
      rw [bankComponentKernel,← SphericalAging.FiniteModel.tensorMonomial_gram]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      ring_nf
    · simp only [hi,ite_false,Finset.sum_const_zero]
  rw [he]
  simp only [amplitudeProbe_condition_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The source integration-by-parts kernel has the literal cross-latitude
amplitude factors and the true transverse inner product normalization. -/
theorem selectedKernel_amplitudeBankLinear_physical (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (u v : Vector (n+1)) :
    selectedKernel (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) u v=
      β^2*(n+1:ℝ)*mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1):ℝ)*
        (overlap x u*overlap x v)^(p₀.val.val-(k.val+1))*
        ((inner ℝ (e.toContinuousLinearMap.adjoint u) (e.toContinuousLinearMap.adjoint v))/(n+1:ℝ))^(k.val+1) := by
  rw [selectedKernel_amplitudeBankLinear_eq,bankComponentKernel_eq]
  simp only [amplitudeProbeIndex]
  ring

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
