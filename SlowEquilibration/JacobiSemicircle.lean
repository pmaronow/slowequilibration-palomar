-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ResolventDensity
public import SlowEquilibration.SemicircleInsidePotential

/-! Genuine deterministic Jacobi empirical convergence to the literal
semicircle law for every continuous test function. Uniformly bounded integral
functionals extend actual outside-resolvent convergence across the proved dense
linear span; no semicircle weak-convergence premise is assumed. -/

@[expose] public section
namespace SlowEquilibration.JacobiSemicircle

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter ContinuousMap
open scoped Topology BigOperators
open ResolventDensity OAI.CriticalSK GOELogPotential SemicirclePotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def semicircleLawOnK : Measure K := SemicirclePotential.law.comap ((↑) : K → ℝ)

instance : IsProbabilityMeasure semicircleLawOnK where
  measure_univ := by
    rw [semicircleLawOnK,comap_subtype_coe_apply measurableSet_Icc,Set.image_univ,Subtype.range_coe]
    have h := measure_add_measure_compl (μ := SemicirclePotential.law) (s := Icc (-2:ℝ) 2) measurableSet_Icc
    simpa only [law_supported,add_zero,measure_univ] using h

lemma continuous_test_integrable (μ : Measure K) [IsProbabilityMeasure μ] (f : C(K,ℝ)) :
    Integrable f μ :=
  (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
    (ae_of_all _ f.norm_coe_le_norm)

def probabilityIntegral (μ : Measure K) [IsProbabilityMeasure μ] : C(K,ℝ) →L[ℝ] ℝ :=
  (show C(K,ℝ) →ₗ[ℝ] ℝ from
    { toFun := fun f => ∫ x,f x ∂μ
      map_add' := fun f g => by
        change (∫ x,f x+g x ∂μ)=(∫ x,f x ∂μ)+(∫ x,g x ∂μ)
        exact integral_add (continuous_test_integrable μ f) (continuous_test_integrable μ g)
      map_smul' := fun r f => by
        change (∫ x,r*f x ∂μ)=r*(∫ x,f x ∂μ)
        exact integral_const_mul r f }).mkContinuous 1 (fun f => by
    change ‖∫ x,f x ∂μ‖≤1*‖f‖
    have h := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ f.norm_coe_le_norm)
    simpa only [probReal_univ,mul_one,one_mul] using h)

@[simp] lemma probabilityIntegral_apply (μ : Measure K) [IsProbabilityMeasure μ] (f : C(K,ℝ)) :
    probabilityIntegral μ f=∫ x,f x ∂μ := rfl

lemma probabilityIntegral_resolvent (a : Pole) :
    probabilityIntegral semicircleLawOnK (ResolventDensity.resolvent a)=
      SemicirclePotential.resolvent a.val := by
  change (∫ x : K,(a.val-x.val)⁻¹ ∂SemicirclePotential.law.comap ((↑) : K → ℝ))=_
  rw [integral_subtype_comap (μ := SemicirclePotential.law) (s := Icc (-2:ℝ) 2) measurableSet_Icc (fun x : ℝ => (a.val-x)⁻¹),
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr law_supported),integral_law_interval]
  unfold SemicirclePotential.resolvent
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  ring

def jacobiPoint (n : ℕ) (i : Fin (n+1)) : K :=
  ⟨2-orderedJacobiGaps n i,by
    constructor
    · linarith [orderedJacobiGaps_le_four n i]
    · linarith [orderedJacobiGaps_nonneg n i]⟩

def jacobiIntegral (n : ℕ) : C(K,ℝ) →L[ℝ] ℝ :=
  (show C(K,ℝ) →ₗ[ℝ] ℝ from
    { toFun := fun f => (∑ i,f (jacobiPoint n i))/(n+1 : ℝ)
      map_add' := fun f g => by simp only [ContinuousMap.add_apply,Finset.sum_add_distrib,add_div]
      map_smul' := fun r f => by
        simp only [ContinuousMap.smul_apply,smul_eq_mul,← Finset.mul_sum,RingHom.id_apply]
        ring }).mkContinuous 1 (fun f => by
    change |(∑ i,f (jacobiPoint n i))/(n+1 : ℝ)|≤1*‖f‖
    rw [abs_div,abs_of_pos (by positivity : 0<(n+1 : ℝ))]
    apply (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mpr
    calc
      _≤∑ i : Fin (n+1),|f (jacobiPoint n i)| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _i : Fin (n+1),‖f‖ := Finset.sum_le_sum fun i _ => f.norm_coe_le_norm _
      _=_ := by simp;ring)

@[simp] lemma jacobiIntegral_apply (n : ℕ) (f : C(K,ℝ)) :
    jacobiIntegral n f=(∑ i,f (jacobiPoint n i))/(n+1 : ℝ) := rfl

lemma jacobiIntegral_norm_le (n : ℕ) (f : C(K,ℝ)) : ‖jacobiIntegral n f‖≤‖f‖ := by
  change |(∑ i,f (jacobiPoint n i))/(n+1 : ℝ)|≤‖f‖
  rw [abs_div,abs_of_pos (by positivity : 0<(n+1 : ℝ))]
  apply (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mpr
  calc
    _≤∑ i : Fin (n+1),|f (jacobiPoint n i)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ _i : Fin (n+1),‖f‖ := Finset.sum_le_sum fun i _ => f.norm_coe_le_norm _
    _=_ := by simp;ring

lemma jacobiIntegral_equicontinuous : Equicontinuous (fun n : ℕ => (jacobiIntegral n : C(K,ℝ) → ℝ)) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun r => r) tendsto_id
  intro f g n
  rw [dist_eq_norm,← map_sub,dist_eq_norm]
  exact jacobiIntegral_norm_le n (f-g)

lemma jacobi_resolvent_tendsto (a : Pole) :
    Tendsto (fun n => jacobiIntegral n (ResolventDensity.resolvent a)) atTop
      (𝓝 (probabilityIntegral semicircleLawOnK (ResolventDensity.resolvent a))) := by
  rw [probabilityIntegral_resolvent,SemicirclePotential.resolvent_eq_semicircleResolvent a.prop]
  let s : ℝ := a.val-2
  have hs : 0<s := sub_pos.mpr a.prop
  have hbound := jacobi_resolvent_error_uniform_eventually (a := s) (b := s) hs
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have ht : Tendsto (fun n : ℕ => 2/((n+1 : ℝ)*s)) atTop (𝓝 0) :=
    (hn.atTop_mul_const hs).const_div_atTop 2
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have he := ht.eventually (gt_mem_nhds heps)
  filter_upwards [hbound,he] with n hb he
  have hh := hb s (by simp)
  have hf : jacobiIntegral n (ResolventDensity.resolvent a)=jacobiNormalizedResolvent n s := by
    simp only [jacobiIntegral_apply,jacobiNormalizedResolvent]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change (a.val-(2-orderedJacobiGaps n i))⁻¹=(s+orderedJacobiGaps n i)⁻¹
    congr 1
    dsimp only [s]
    ring
  rw [hf]
  exact hh.trans_lt he

def convergenceSpace : Submodule ℝ C(K,ℝ) where
  carrier := {f | Tendsto (fun n => jacobiIntegral n f) atTop
    (𝓝 (probabilityIntegral semicircleLawOnK f))}
  zero_mem' := by
    change Tendsto (fun n => jacobiIntegral n 0) atTop (𝓝 (probabilityIntegral semicircleLawOnK 0))
    simp only [map_zero]
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun n => jacobiIntegral n (f+g)) atTop (𝓝 (probabilityIntegral semicircleLawOnK (f+g)))
    simpa only [map_add] using hf.add hg
  smul_mem' := by
    intro r f hf
    change Tendsto (fun n => jacobiIntegral n (r • f)) atTop (𝓝 (probabilityIntegral semicircleLawOnK (r • f)))
    simpa only [map_smul,smul_eq_mul] using hf.const_mul r

lemma convergenceSpace_closed : IsClosed (convergenceSpace : Set C(K,ℝ)) :=
  jacobiIntegral_equicontinuous.isClosed_setOfPred_tendsto (probabilityIntegral semicircleLawOnK).continuous

lemma generators_converge : generators⊆convergenceSpace := by
  intro f hf
  rcases hf with rfl | ⟨a,rfl⟩
  · change Tendsto (fun n => jacobiIntegral n 1) atTop (𝓝 (probabilityIntegral semicircleLawOnK 1))
    have hj (n : ℕ) : jacobiIntegral n 1=1 := by
      simp only [jacobiIntegral_apply,ContinuousMap.one_apply,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one]
      exact div_self (by positivity)
    have hm : probabilityIntegral semicircleLawOnK 1=1 := by simp
    rw [hm]
    have ht : (fun n : ℕ => jacobiIntegral n 1)=(fun _ : ℕ => (1:ℝ)) := funext hj
    rw [ht]
    exact tendsto_const_nhds
  · exact jacobi_resolvent_tendsto a

/-- The actual bounded Jacobi eigenvalues converge to the actual semicircle
law for every continuous function, derived solely from proved resolvent limits. -/
theorem continuous_test_tendsto (f : C(K,ℝ)) :
    Tendsto (fun n => (∑ i,f (jacobiPoint n i))/(n+1 : ℝ)) atTop
      (𝓝 (∫ x,f x ∂semicircleLawOnK)) := by
  have hh : ResolventDensity.spanClosure≤convergenceSpace :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr generators_converge)
      convergenceSpace_closed
  rw [ResolventDensity.spanClosure_eq_top] at hh
  exact hh (show f∈(⊤ : Submodule ℝ C(K,ℝ)) from trivial)

lemma subtype_hasLaw : HasLaw ((↑) : K → ℝ) SemicirclePotential.law semicircleLawOnK := by
  refine ⟨measurable_subtype_coe.aemeasurable,?_⟩
  rw [semicircleLawOnK,map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr law_supported)]

/-- Literal scalar version of the continuous-test semicircle law. -/
theorem continuous_test_tendsto_real (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => (∑ i,f (2-orderedJacobiGaps n i))/(n+1 : ℝ)) atTop
      (𝓝 (∫ t,f t ∂SemicirclePotential.law)) := by
  let F : C(K,ℝ) := ⟨fun x => f x.val,hf.comp continuous_subtype_val⟩
  have ht := continuous_test_tendsto F
  have he : (∫ x : K,F x ∂semicircleLawOnK)=∫ t,f t ∂SemicirclePotential.law :=
    subtype_hasLaw.integral_comp hf.aestronglyMeasurable
  rw [he] at ht
  exact ht

end
end SlowEquilibration.JacobiSemicircle
