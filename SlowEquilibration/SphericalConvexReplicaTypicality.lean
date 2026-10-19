-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalEvenReplicaTypicality
public import SlowEquilibration.SphericalConvexLikelihoodTransfer
public import SlowEquilibration.SphericalConvexHSTypicality

@[expose] public section

/-! # Actual exponential replica typicality for globally convex covariance -/
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal exponential typical-reference assertion for every finite mixture with covariance convex on [-1,1] below its static threshold. The disorder event and the
reference set are both Borel and constructed from the actual partition. -/
theorem convex_replica_typicality (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ Ω : Set (Disorder (n+1) μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw (n+1) μ.maxDegree).real Ωᶜ ≤ Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        ∀ J ∈ Ω, ∃ T : Set (Vector (n+1)), MeasurableSet T ∧
          T ⊆ {u | ‖u‖^2=((n+1 : ℕ) : ℝ)} ∧
          (gibbsLaw (n+1) β (fieldOfMixture μ J)).real Tᶜ ≤ Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
          ∀ u ∈ T, (gibbsLaw (n+1) β (fieldOfMixture μ J)).real {v | δ ≤ |overlap u v|} ≤
            Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨η,γ,hη,hγ,hplant⟩ := convex_hs_planted_typicality μ hconv hβ hβs hδ
  let r := plantedTransferRate μ β γ
  have hr : 0 < r := plantedTransferRate_pos μ hβ hγ
  let k := (η/2)^2/(8*β^2*μ.xi 1)
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  have hk : 0 < k := by dsimp [k]; positivity
  let t := min k (r/2)
  have ht : 0 < t := lt_min hk (half_pos hr)
  let c := min (t/2) (η/2)
  have hc : 0 < c := lt_min (half_pos ht) (half_pos hη)
  have hlim := convex_quenchedPressure_tendsto_annealed_le_static μ hconv hβ.le hβs.le
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
