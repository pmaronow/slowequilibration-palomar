-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeModel

@[expose] public section

/-! # Covariance of the literal plateau amplitude bank

The selected Gaussian probes have the actual polynomial kernel required
for amplitude integration by parts, including their cross-latitude factors.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel
open scoped BigOperators Topology InnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def bankComponentScale (μ : FiniteMixture) (x : Vector (n+1))
    (i : BankIndex μ) (u : Vector (n+1)) : ℝ :=
  Real.sqrt (n+1:ℝ)*bankCoefficient μ i*overlap x u^(i.1.val.val-i.2.val)*
    ((Real.sqrt (n+1:ℝ))⁻¹)^i.2.val

def bankComponentKernel (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ) (u v : Vector (n+1)) : ℝ :=
  bankComponentScale μ x i u*bankComponentScale μ x i v*
    (inner ℝ (e.toContinuousLinearMap.adjoint u) (e.toContinuousLinearMap.adjoint v))^i.2.val

lemma bankComponent_eq_scaled (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ)
    (D : SphericalAging.FiniteModel.Disorder n i.2.val) (u : Vector (n+1)) :
    bankComponent μ x e i D u=bankComponentScale μ x i u*
      SphericalAging.FiniteModel.tensorLinear
        (SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u)) D := rfl

lemma tensorLinear_probability_covariance {k : ℕ} (u v : Vector n) :
    covariance (SphericalAging.FiniteModel.tensorLinear (SphericalAging.FiniteModel.tensorMonomial u))
      (SphericalAging.FiniteModel.tensorLinear (SphericalAging.FiniteModel.tensorMonomial v))
      (SphericalAging.FiniteModel.disorderLaw n k)=(inner ℝ u v)^k := by
  rw [covariance_eq_sub (SphericalAging.FiniteModel.tensorLinear_memLp _)
    (SphericalAging.FiniteModel.tensorLinear_memLp _)]
  simp only [SphericalAging.FiniteModel.tensorLinear_mean,mul_zero,sub_zero]
  exact (SphericalAging.FiniteModel.tensorLinear_covariance _ _).trans
    (SphericalAging.FiniteModel.tensorMonomial_gram u v)

theorem bankComponent_memLp (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ) (u : Vector (n+1)) :
    MemLp (fun D : BankDisorder n μ => bankComponent μ x e i (D i) u) 2 (bankLaw n μ) := by
  simp only [bankComponent_eq_scaled]
  exact ((SphericalAging.FiniteModel.tensorLinear_memLp _).const_mul _).comp_measurePreserving
    (measurePreserving_eval _ i)

theorem bankComponent_mean (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ) (u : Vector (n+1)) :
    (∫ D : BankDisorder n μ, bankComponent μ x e i (D i) u ∂bankLaw n μ)=0 := by
  simp only [bankComponent_eq_scaled,bankLaw]
  rw [integral_comp_eval
    (μ := fun j : BankIndex μ => SphericalAging.FiniteModel.disorderLaw n j.2.val)
    (i := i) (f := fun T => bankComponentScale μ x i u*SphericalAging.FiniteModel.tensorLinear
      (SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u)) T)
    ((SphericalAging.FiniteModel.tensorLinear_memLp _).const_mul _).aestronglyMeasurable]
  rw [integral_const_mul,SphericalAging.FiniteModel.tensorLinear_mean,mul_zero]

/-- Distinct bank blocks are genuinely independent under the actual law;
the diagonal term is the exact cross-latitude polynomial probe kernel. -/
theorem bankComponent_covariance (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i j : BankIndex μ) (u v : Vector (n+1)) :
    covariance (fun D : BankDisorder n μ => bankComponent μ x e i (D i) u)
      (fun D => bankComponent μ x e j (D j) v) (bankLaw n μ)=
      if i=j then bankComponentKernel μ x e i u v else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    have hmap : (bankLaw n μ).map (fun D : BankDisorder n μ => D i)=
        SphericalAging.FiniteModel.disorderLaw n i.2.val := (bankBlock_hasLaw n μ i).map_eq
    have hcov := covariance_map_fun (μ := bankLaw n μ) (Z := fun D : BankDisorder n μ => D i)
      (X := fun T => bankComponent μ x e i T u) (Y := fun T => bankComponent μ x e i T v)
      (by rw [hmap]; simpa only [bankComponent_eq_scaled] using
        ((SphericalAging.FiniteModel.tensorLinear_memLp _).const_mul _).aestronglyMeasurable)
      (by rw [hmap]; simpa only [bankComponent_eq_scaled] using
        ((SphericalAging.FiniteModel.tensorLinear_memLp _).const_mul _).aestronglyMeasurable)
      (bankBlock_hasLaw n μ i).aemeasurable
    rw [hmap] at hcov
    rw [← hcov]
    simp only [bankComponent_eq_scaled,covariance_const_mul_left,covariance_const_mul_right]
    rw [tensorLinear_probability_covariance]
    unfold bankComponentKernel
    ring
  · rw [ite_eq_right hij]
    have hmi : Measurable (fun T => bankComponent μ x e i T u) := by
      have he : (fun T => bankComponent μ x e i T u)=bankComponentCLM μ x e i u := by
        funext T
        exact (bankComponentCLM_apply μ x e i u T).symm
      rw [he]
      exact (bankComponentCLM μ x e i u).measurable
    have hmj : Measurable (fun T => bankComponent μ x e j T v) := by
      have he : (fun T => bankComponent μ x e j T v)=bankComponentCLM μ x e j v := by
        funext T
        exact (bankComponentCLM_apply μ x e j v T).symm
      rw [he]
      exact (bankComponentCLM μ x e j v).measurable
    exact ((bank_independent n μ).indepFun hij |>.comp hmi hmj).covariance_eq_zero
      (bankComponent_memLp μ x e i u) (bankComponent_memLp μ x e j v)

theorem amplitudeField_mean (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) :
    (∫ D : BankDisorder n μ, amplitudeField μ x e p₀ s D u ∂bankLaw n μ)=0 := by
  unfold amplitudeField
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul,bankComponent_mean]
    simp only [mul_zero,Finset.sum_const_zero]
  · intro i _
    exact ((bankComponent_memLp μ x e i u).integrable (by norm_num)).const_mul _

/-- Exact covariance of the actual perturbed Gaussian polynomial. No
thermodynamic or overlap-concentration premise enters this identity. -/
theorem amplitudeField_covariance (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u v : Vector (n+1)) :
    covariance (fun D : BankDisorder n μ => amplitudeField μ x e p₀ s D u)
      (fun D => amplitudeField μ x e p₀ s D v) (bankLaw n μ)=
      ∑ i : BankIndex μ, bankAmplitude p₀ s i^2*bankComponentKernel μ x e i u v := by
  classical
  unfold amplitudeField
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left,covariance_const_mul_right,bankComponent_covariance]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      ring
    · intro j _ hji
      simp only [ite_eq_right (Ne.symm hji),mul_zero]
    · simp
  · intro i
    exact (bankComponent_memLp μ x e i u).const_mul _
  · intro i
    exact (bankComponent_memLp μ x e i v).const_mul _

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
