-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPositivePartitionUpper
public import SlowEquilibration.PlantedTrialGeometry
public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics
public import SlowEquilibration.SphericalPlantedConditionalBound
public import SlowEquilibration.SphericalOverlapPartitionMeasurable

/-! Actual planted restricted-partition upper tails on signed overlap
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

theorem convex_signed_profile_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β M ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) {A : Set ℝ}
    (htrial : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → plantedProfileTrial μ β |q| ≤ M) :
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
      by_cases hqρ : |q| ≤ ρ
      · refine ⟨q,abs_le.mp hqρ,?_⟩
        linarith [htrial q hqA hq]
      · have habs : |q| ∈ Ico ρ 1 := by
          exact ⟨(lt_of_not_ge hqρ).le,abs_lt.mpr hq⟩
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
signed-overlap region on which the literal scalar trial is bounded. -/
theorem convex_planted_signed_partition_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β M ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) {A : Set ℝ} (hA : MeasurableSet A)
    (htrial : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → plantedProfileTrial μ β |q| ≤ M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop,
      plantedLaw (mixtureCoefficients μ) β (positivePartitionUpperBadEvent N μ β M ε A) ≤
        ENNReal.ofReal (Real.exp (-γ * (N : ℝ))) := by
  obtain ⟨γ,hγ,hprofile⟩ := convex_signed_profile_upper_tail μ hconv hβ (half_pos hε) htrial
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

/-- The same signed estimate before integrating over the reference, with
the genuine translated disorder at every spherical reference point. -/
theorem convex_shifted_signed_partition_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β M ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) {A : Set ℝ} (hA : MeasurableSet A)
    (htrial : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → plantedProfileTrial μ β |q| ≤ M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (u : Vector N), ‖u‖^2=(N : ℝ) →
        disorderLaw N μ.maxDegree {J | Real.exp ((N : ℝ)*(M+ε)) <
          overlapRestrictedPartition (mixtureCoefficients μ) β A
            (J+plantedShift (mixtureCoefficients μ) β u,u)} ≤
          ENNReal.ofReal (Real.exp (-γ*(N : ℝ))) := by
  obtain ⟨γ,hγ,hprofile⟩ := convex_signed_profile_upper_tail μ hconv hβ (half_pos hε) htrial
  have hb : ∀ᶠ n : ℕ in atTop, ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      disorderLaw (n+1) μ.maxDegree {J | Real.exp (((n+1 : ℕ) : ℝ)*(M+ε)) <
        overlapRestrictedPartition (mixtureCoefficients μ) β A
          (J+plantedShift (mixtureCoefficients μ) β u,u)} ≤
        ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
    filter_upwards [hprofile,partitionOn_eventually_le_of_latitudeProfile_upper (half_pos hε)]
      with n hprofile hlap
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
    rw [show M+ε/2+ε/2=M+ε by ring] at hz
    exact (not_lt_of_ge hz) hJ
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hb
  refine ⟨γ,hγ,eventually_atTop.2 ⟨n₀+1,?_⟩⟩
  intro N hN
  obtain ⟨m,rfl⟩ : ∃ m : ℕ,N=m+1 := ⟨N-1,by omega⟩
  exact hn₀ m (by omega)

theorem plantedProfileTrial_le_annealed_substatic (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 ≤ β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hq : q ∈ Ico (0 : ℝ) 1) :
    plantedProfileTrial μ β q ≤ β^2*μ.xi 1/2 := by
  have hPhi : Thresholds.Phi μ.xi β q ≤ 0 := by
    by_cases hq0 : q=0
    · subst q
      simp [Thresholds.Phi,μ.xi_zero]
    · exact (μ.Phi_nonpos_iff_le_staticThreshold hβ).mpr hβs q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0),hq.2⟩
  rw [plantedProfileTrial_eq_annealed_add_Phi]
  linarith

/-- Genuine full planted partition upper tail, including all negative
overlaps, for every actual reference point. -/
theorem convex_shifted_full_partition_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β ε : ℝ}
    (hβ : 0 < β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (u : Vector N), ‖u‖^2=(N : ℝ) →
        disorderLaw N μ.maxDegree {J | Real.exp ((N : ℝ)*(β^2*μ.xi 1/2+ε)) <
          partition N β (fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β u))} ≤
          ENNReal.ofReal (Real.exp (-γ*(N : ℝ))) := by
  obtain ⟨γ,hγ,hbound⟩ := convex_shifted_signed_partition_upper_tail μ hconv hβ hε
    (A := univ) MeasurableSet.univ (fun q _ hq => plantedProfileTrial_le_annealed_substatic μ hβ.le hβs
      ⟨abs_nonneg q,abs_lt.mpr hq⟩)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hbound] with N hN
  intro u hu
  simpa only [overlapRestrictedPartition,mem_univ,Set.ofPred_true,partitionOn,
    Measure.restrict_univ,fieldOfMixture,partition] using hN u hu

end
end SlowEquilibration.SphericalModel
