-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalEvenRSLower
public import SlowEquilibration.SphericalGoodReference
public import SlowEquilibration.SphericalExponentialTransfer

@[expose] public section

/-! Genuine exponential Gibbs replica typicality for even mixtures in the
strict RS phase. The Borel good set is constructed from the actual HS
truncation, and all probabilities concern the original tensor disorder. -/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def hsGoodDisorder {N P : ℕ} (c : Degree P → ℝ) (β δ η a : ℝ) : Set (Disorder N P) :=
  {J | |Real.log (partition N β (field c J))/(N : ℝ)-β^2*covariancePolynomial c 1/2| ≤ η/2 ∧
    referenceBadMass c β (hsTruncation c β δ (annealedExponent N c β-(N : ℝ)*η))ᶜ J ≤ a}

theorem hsGoodDisorder_measurable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β δ η a : ℝ) : MeasurableSet (hsGoodDisorder (N := N) c β δ η a) := by
  have hp := continuous_abs.measurable.comp
    (((partition_measurable (N := N) c β).log.div_const (N : ℝ)).sub_const
      (β^2*covariancePolynomial c 1/2))
  exact (measurableSet_le hp measurable_const).inter
    (measurableSet_le (referenceBadMass_measurable hN c β
      (hsTruncation_measurable c β δ _).compl) measurable_const)

theorem hsGoodDisorder_failure_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β δ η : ℝ) {a : ℝ} (ha : 0 < a) :
    (disorderLaw N P).real (hsGoodDisorder c β δ η a)ᶜ ≤
      (disorderLaw N P).real {J |
        η/2 < |Real.log (partition N β (field c J))/(N : ℝ)-β^2*covariancePolynomial c 1/2|} +
      (gibbsReferenceLaw (N := N) c β).real
        (hsTruncation c β δ (annealedExponent N c β-(N : ℝ)*η))ᶜ/a := by
  let E := (hsTruncation (N := N) c β δ (annealedExponent N c β-(N : ℝ)*η))ᶜ
  have hE : MeasurableSet E := (hsTruncation_measurable c β δ _).compl
  have hm := goodReferenceSet_failure_le hN c β hE ha
  simp only [goodReferenceSet_compl_mass_eq hN c β E] at hm
  have heq : (hsGoodDisorder c β δ η a)ᶜ =
      {J : Disorder N P | η/2 < |Real.log (partition N β (field c J))/(N : ℝ)-β^2*covariancePolynomial c 1/2|} ∪
        {J | a < referenceBadMass c β E J} := by
    ext J
    simp only [hsGoodDisorder,mem_compl_iff,mem_ofPred_eq,mem_union,not_and_or,not_le,E]
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add le_rfl hm)

/-- An actual HS-good disorder realization supplies a Borel spherical set
of references with exponentially small far-overlap Gibbs mass. -/
theorem hsGoodDisorder_has_typical_set {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β δ η a : ℝ) {J : Disorder N P}
    (hJ : J ∈ hsGoodDisorder c β δ η a) :
    ∃ T : Set (Vector N), MeasurableSet T ∧ T ⊆ {u | ‖u‖^2=(N : ℝ)} ∧
      (gibbsLaw N β (field c J)).real Tᶜ ≤ a ∧ ∀ u ∈ T,
        (gibbsLaw N β (field c J)).real {v | δ ≤ |overlap u v|} ≤
          Real.exp (-(η/2)*(N : ℝ)) := by
  let E := (hsTruncation (N := N) c β δ (annealedExponent N c β-(N : ℝ)*η))ᶜ
  have hE : MeasurableSet E := (hsTruncation_measurable c β δ _).compl
  refine ⟨goodReferenceSet E J,goodReferenceSet_measurable hE J,
    goodReferenceSet_subset_sphere E J,?_,?_⟩
  · rw [goodReferenceSet_compl_mass_eq hN c β E]
    exact hJ.2
  · intro u hu
    have huT : (J,u) ∈ hsTruncation c β δ (annealedExponent N c β-(N : ℝ)*η) :=
      not_not.mp hu.2
    change overlapPartition c β (smallOverlap δ)ᶜ J u ≤
      Real.exp (annealedExponent N c β-(N : ℝ)*η) at huT
    rw [overlapPartition_far_eq_partitionOn] at huT
    have hs : {v : Vector N | δ ≤ |overlap u v|} = overlapRegion u (farOverlapRegion δ) := by
      ext v
      simp only [mem_ofPred_eq,overlapRegion,farOverlapRegion]
      unfold overlap
      rw [real_inner_comm]
    rw [hs,gibbsLaw_real_eq_partitionOn_div hN β (field_contDiff c J).continuous
      (overlapRegion_measurable u (farOverlapRegion_measurable δ))]
    have hZ := (partition_bounds_of_pressure_tolerance hN β (field_contDiff c J).continuous hJ.1).1
    calc
      _ ≤ Real.exp (annealedExponent N c β-(N : ℝ)*η)/
          Real.exp ((N : ℝ)*(β^2*covariancePolynomial c 1/2-η/2)) :=
        div_le_div₀ (Real.exp_pos _).le huT (Real.exp_pos _) hZ
      _ = _ := by rw [← Real.exp_sub]; unfold annealedExponent; congr 1; ring

theorem weighted_exponential_eventually_le {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C*Real.exp (-a*((n+1 : ℕ) : ℝ)) ≤
      Real.exp (-(a/2)*((n+1 : ℕ) : ℝ)) := by
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ => C*Real.exp (-(a/2)*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop (half_pos ha))).const_mul C
    simpa only [Function.comp_apply,neg_mul,mul_zero] using h
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with n hn
  have he : Real.exp (-a*((n+1 : ℕ) : ℝ)) =
      Real.exp (-(a/2)*((n+1 : ℕ) : ℝ))*Real.exp (-(a/2)*((n+1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hn.le (Real.exp_pos _).le).trans_eq (one_mul _)

/-- The literal exponential typical-reference assertion for every even
finite mixture below its static threshold. The disorder event and the
reference set are both Borel and constructed from the actual partition. -/
theorem even_replica_typicality (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) {β δ : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ Ω : Set (Disorder (n+1) μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw (n+1) μ.maxDegree).real Ωᶜ ≤ Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        ∀ J ∈ Ω, ∃ T : Set (Vector (n+1)), MeasurableSet T ∧
          T ⊆ {u | ‖u‖^2=((n+1 : ℕ) : ℝ)} ∧
          (gibbsLaw (n+1) β (fieldOfMixture μ J)).real Tᶜ ≤ Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
          ∀ u ∈ T, (gibbsLaw (n+1) β (fieldOfMixture μ J)).real {v | δ ≤ |overlap u v|} ≤
            Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨η,γ,hη,hγ,hplant⟩ := even_hs_planted_typicality μ heven hβ hβs hδ
  let r := plantedTransferRate μ β γ
  have hr : 0 < r := plantedTransferRate_pos μ hβ hγ
  let k := (η/2)^2/(8*β^2*μ.xi 1)
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  have hk : 0 < k := by dsimp [k]; positivity
  let t := min k (r/2)
  have ht : 0 < t := lt_min hk (half_pos hr)
  let c := min (t/2) (η/2)
  have hc : 0 < c := lt_min (half_pos ht) (half_pos hη)
  have hlim := even_quenchedPressure_tendsto_annealed μ heven hβ hβs
  have hgap := (Metric.tendsto_nhds.mp (hlim.comp (tendsto_add_atTop_nat 1))) (γ/4) (by positivity)
  have hconc := (tendsto_add_atTop_nat 1).eventually
    (annealed_logPartition_concentration_eventually_of_pressure_limit μ hβ hlim (half_pos hη))
  refine ⟨c,hc,?_⟩
  filter_upwards [hplant,hgap,hconc,weighted_exponential_eventually_le ht 5] with n hplant hgap hconc htail
  let N := n+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  let coeff := mixtureCoefficients μ
  let E := (hsTruncation (N := N) coeff β δ (annealedExponent N coeff β-(N : ℝ)*η))ᶜ
  have hE : MeasurableSet E := (hsTruncation_measurable coeff β δ _).compl
  have hP : (plantedLaw coeff β).real E ≤ Real.exp (-γ*(N : ℝ)) := by
    let : IsProbabilityMeasure (plantedLaw (N := N) coeff β) :=
      plantedLaw_probability hN coeff (mixtureCoefficients_nonnegative μ) β
    have hs := measureReal_add_measureReal_compl (μ := plantedLaw (N := N) coeff β)
      (hsTruncation_measurable coeff β δ (annealedExponent N coeff β-(N : ℝ)*η))
    rw [probReal_univ] at hs
    change 1-Real.exp (-γ*(N : ℝ)) ≤
      (plantedLaw coeff β).real (hsTruncation coeff β δ (annealedExponent N coeff β-(N : ℝ)*η)) at hplant
    dsimp [E]
    linarith
  have hQ : (gibbsReferenceLaw coeff β).real E ≤ 3*Real.exp (-r*(N : ℝ)) :=
    exponential_planted_transfer_of_pressure_gap hN μ hβ hγ
      (by simpa only [Real.dist_eq,Function.comp_apply,N] using hgap.le) hE hP
  let a := Real.exp (-(r/2)*(N : ℝ))
  let Ω := hsGoodDisorder (N := N) coeff β δ η a
  have hscalar (s : ℝ) (hs : c ≤ s) : Real.exp (-s*(N : ℝ)) ≤ Real.exp (-c*(N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hct : c ≤ t/2 := min_le_left _ _
  have hcr : c ≤ r/2 := hct.trans (by have hh := min_le_right k (r/2); dsimp [t] at *; linarith)
  have hcη : c ≤ η/2 := min_le_right _ _
  refine ⟨Ω,hsGoodDisorder_measurable hN coeff β δ η a,?_,?_⟩
  · have hf := hsGoodDisorder_failure_le hN coeff β δ η (a := a) (Real.exp_pos _)
    have hdiv := div_le_div_of_nonneg_right hQ (Real.exp_pos (-(r/2)*(N : ℝ))).le
    have he : 3*Real.exp (-r*(N : ℝ))/a = 3*Real.exp (-(r/2)*(N : ℝ)) := by
      dsimp [a]
      rw [mul_div_assoc,← Real.exp_sub]
      congr 2
      ring
    rw [he] at hdiv
    have hconc' : (disorderLaw N μ.maxDegree).real
        {J | η/2 < |Real.log (partition N β (field coeff J))/(N : ℝ)-β^2*covariancePolynomial coeff 1/2|} ≤
          2*Real.exp (-k*(N : ℝ)) := by
      have he : -k*(N : ℝ) = -((η/2)^2*(N : ℝ))/(8*β^2*μ.xi 1) := by
        dsimp [k]
        ring
      rw [he]
      have hpart (J : Disorder N μ.maxDegree) : mixturePartition μ β J =
          partition N β (field coeff J) := rfl
      simp_rw [hpart] at hconc
      simpa only [coeff,covariancePolynomial_mixture,N] using hconc
    have hkt : Real.exp (-k*(N : ℝ)) ≤ Real.exp (-t*(N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hh := min_le_left k (r/2)
      change -(k)*(N : ℝ) ≤ -(min k (r/2))*(N : ℝ)
      nlinarith
    have hrt : Real.exp (-(r/2)*(N : ℝ)) ≤ Real.exp (-t*(N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hh := min_le_right k (r/2)
      change -(r/2)*(N : ℝ) ≤ -(min k (r/2))*(N : ℝ)
      nlinarith
    have hf' : (disorderLaw N μ.maxDegree).real Ωᶜ ≤ 5*Real.exp (-t*(N : ℝ)) := by
      change (disorderLaw N μ.maxDegree).real (hsGoodDisorder coeff β δ η a)ᶜ ≤ _
      linarith
    exact hf'.trans (htail.trans (hscalar (t/2) hct))
  · intro J hJ
    obtain ⟨T,hT,hTs,hTm,hfar⟩ := hsGoodDisorder_has_typical_set hN coeff β δ η a hJ
    exact ⟨T,hT,hTs,hTm.trans (hscalar (r/2) hcr),fun u hu =>
      (hfar u hu).trans (hscalar (η/2) hcη)⟩

end SlowEquilibration.SphericalModel
