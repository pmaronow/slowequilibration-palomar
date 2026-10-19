-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexPlantedProfile
public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics
public import SlowEquilibration.SphericalPlantedConditionalBound
public import SlowEquilibration.SphericalOverlapPartitionMeasurable

/-! Actual planted restricted-partition upper tails on positive overlap
regions. The scalar trial bound is integrated against the genuine coarea
measure, with the polar region controlled by actual field regularity. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def positivePartitionUpperBadEvent (N : ℕ) (μ : FiniteMixture) (β M ε : ℝ)
    (A : Set ℝ) : Set (Disorder N μ.maxDegree × Vector N) :=
  {z | Real.exp ((N : ℝ) * (M + ε)) < overlapRestrictedPartition (mixtureCoefficients μ) β A z}

theorem positivePartitionUpperBadEvent_measurable (N : ℕ) (μ : FiniteMixture)
    (β M ε : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (positivePartitionUpperBadEvent N μ β M ε A) :=
  measurableSet_lt measurable_const (overlapRestrictedPartition_measurable _ _ hA)

theorem convex_positive_profile_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β M ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) {A : Set ℝ}
    (hpos : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → 0 ≤ q)
    (htrial : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → plantedProfileTrial μ β q ≤ M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u = 0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 ∧
          M + ε < plantedLatitudeProfile n μ β u e q J} ≤
            ENNReal.ofReal (Real.exp (-γ * ((n+1 : ℕ) : ℝ))) := by
  obtain ⟨ρ,hρ,hpole⟩ := plantedLatitudeProfile_signed_pole_event μ hβ.le M (1/2)
    (by constructor <;> norm_num)
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1/2) hρ.1
  obtain ⟨γ₀,hγ₀,hcompact⟩ := convex_plantedLatitudeProfile_eventually_uniform_upper μ hconv
    hβ ⟨hρpos,hρ.2⟩ hε
  obtain ⟨γ,hγ,htail⟩ := latitude_polynomial_tail_eventually_le 0 hγ₀
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hcompact,htail,eventually_ge_atTop 5] with n hcompact htail hn
  intro u hu e he
  let E : Set (Disorder (n+1) μ.maxDegree) := {J | ∃ q ∈ Icc (-ρ) ρ,
    plantedProfileTrial μ β |q| + ε ≤ plantedLatitudeProfile n μ β u e q J}
  have hsub : {J : Disorder (n+1) μ.maxDegree | ∃ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 ∧
      M + ε < plantedLatitudeProfile n μ β u e q J} ⊆ regularDisorderᶜ ∪ E := by
    rintro J ⟨q,hqA,hq,hJ⟩
    by_cases hreg : J ∈ regularDisorder
    · right
      have hq0 := hpos q hqA hq
      by_cases hqρ : q ≤ ρ
      · refine ⟨q,⟨by linarith,hqρ⟩,?_⟩
        rw [abs_of_nonneg hq0]
        linarith [htrial q hqA hq]
      · have habs : |q| ∈ Ico ρ 1 := by
          rw [abs_of_nonneg hq0]
          exact ⟨(lt_of_not_ge hqρ).le,hq.2⟩
        have hp := (hpole n hn).2 J hreg u hu e he q habs
        exact False.elim (by linarith)
    · exact Or.inl hreg
  have hreg : disorderLaw (n+1) μ.maxDegree (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ≤
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ))) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact (hpole n hn).1
  have hcomp : disorderLaw (n+1) μ.maxDegree E ≤
      ENNReal.ofReal (Real.exp (-γ₀ * ((n+1 : ℕ) : ℝ))) := hcompact u hu e he
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add hreg hcomp).trans
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : Real.exp (-((n+1 : ℕ) : ℝ)) ≤ Real.exp (-((n+1 : ℕ) : ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    have hN : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
    linarith
  simp only [pow_zero] at htail
  have hp := Real.exp_pos (-γ₀ * ((n+1 : ℕ) : ℝ))
  linarith

/-- The actual joint planted partition upper-tail estimate for any Borel
positive-overlap region on which the literal scalar trial is bounded. -/
theorem convex_planted_positive_partition_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β M ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → 0 ≤ q)
    (htrial : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → plantedProfileTrial μ β q ≤ M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop,
      plantedLaw (mixtureCoefficients μ) β (positivePartitionUpperBadEvent N μ β M ε A) ≤
        ENNReal.ofReal (Real.exp (-γ * (N : ℝ))) := by
  obtain ⟨γ,hγ,hprofile⟩ := convex_positive_profile_upper_tail μ hconv hβ (half_pos hε) hpos htrial
  have hbound : ∀ᶠ n : ℕ in atTop,
      plantedLaw (mixtureCoefficients μ) β (positivePartitionUpperBadEvent (n+1) μ β M ε A) ≤
        ENNReal.ofReal (Real.exp (-γ * ((n+1 : ℕ) : ℝ))) := by
    filter_upwards [hprofile,partitionOn_eventually_le_of_latitudeProfile_upper (half_pos hε)]
      with n hprofile hlap
    apply planted_measure_le_of_uniform_shift_probability (by omega) (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β (positivePartitionUpperBadEvent_measurable _ μ β M ε hA)
      (Real.exp_pos _).le
    intro u hu
    apply (measure_mono ?_).trans
      (hprofile u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu))
    intro J hJ
    by_contra hbad
    have hgood : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 →
        latitudePartitionProfile n β (field (mixtureCoefficients μ)
          (J+plantedShift (mixtureCoefficients μ) β u)) u q ≤ M+ε/2 := by
      intro q hq hq'
      apply le_of_not_gt
      intro hf
      exact hbad ⟨q,hq,hq',hf⟩
    have hz := hlap β (field (mixtureCoefficients μ) (J+plantedShift (mixtureCoefficients μ) β u))
      (field_contDiff _ _).continuous u hu A hA (M+ε/2) hgood
    have he : M+ε/2+ε/2 = M+ε := by ring
    rw [he] at hz
    exact (not_lt_of_ge hz) hJ
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hbound
  refine ⟨γ,hγ,eventually_atTop.2 ⟨n₀+1,?_⟩⟩
  intro N hN
  obtain ⟨m,rfl⟩ : ∃ m : ℕ,N=m+1 := ⟨N-1,by omega⟩
  exact hn₀ m (by omega)

end
end SlowEquilibration.SphericalModel
