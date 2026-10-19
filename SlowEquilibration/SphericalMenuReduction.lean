-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFullFieldPathKernel
public import SlowEquilibration.SphericalFieldEntryMass
public import SlowEquilibration.ReductionSelectedMenu
public import SlowEquilibration.ReductionInformationEventually

@[expose] public section

/-! # Source finite-menu reduction for the actual complete spherical field

Actual physical semigroups, actual full-field law, singular prescribed
initial laws and the literal joint time/weight infimum specialize the
proved finite-menu reduction. Source support and rotation assumptions are
used only in dimensions N ≥ 2. Capture and the original K_N q_N,M → 0
condition remain explicit analytical premises.
-/

namespace SlowEquilibration.SphericalMenuReduction
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalRotationCovariance SphericalFieldKernels
open SphericalFullFieldPathKernel SphericalReversibility ReductionJointInformation
open ReductionFiniteMenu ReductionEndpointTransfer VaryingProbability
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal ProbabilityTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] mixedTransitionKernel
variable {N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem pullbackBand_rotation_of_full_field (μ : FiniteMixture)
    (B : Set (Field N μ × Vector N))
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ),
      Prod.mk (fieldRotation μ U H) ⁻¹' B = U '' (Prod.mk H ⁻¹' B)) :
    ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J,
      pullbackBand μ B (rotatedDisorder U J) = U '' pullbackBand μ B J := by
  intro U J
  unfold pullbackBand
  rw [← fieldRotation_fieldMap μ U J]
  exact hrot U (fieldMap μ J)

abbrev physicalSemigroup (μ : FiniteMixture) (β : ℝ) (H : Field N μ) :
    ℝ≥0 → Kernel (Vector N) (Vector N) :=
  mixedTransitionKernel μ (coefficientLift μ H) β

def physicalMenuDistance (μ : FiniteMixture) (β : ℝ) (ν : ι → Measure (Vector N))
    (T : ℝ≥0) (H : Field N μ) : ℝ :=
  menuAllTimeDistance (physicalSemigroup μ β H) ν (gibbsKernel μ β H) T

theorem physicalMenuDistance_eq_endpoint (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (ν : ι → Measure (Vector N)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : ℝ≥0) (H : Field N μ) :
    physicalMenuDistance μ β ν T H =
      menuDistance (fun j => evolvedKernel (Kernel.const (Field N μ) (ν j))
        (transitionKernel μ β T) H) (gibbsKernel μ β H) := by
  rw [physicalMenuDistance,menuAllTimeDistance_eq_endpoint _ _ _
    (mixed_kernel_semigroup μ (coefficientLift μ H) β)]
  · congr 1
    funext j
    rw [evolvedKernel_apply_physical]
    rfl
  · intro t
    rw [gibbsKernel_apply]
    exact mixedTransitionKernel_gibbs_invariant hN μ (coefficientLift μ H) β t

theorem physicalMenuDistance_measurable (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (ν : ι → Measure (Vector N)) [∀ j, IsProbabilityMeasure (ν j)] (T : ℝ≥0) :
    Measurable (physicalMenuDistance μ β ν T) := by
  have he : physicalMenuDistance μ β ν T =
      fun H => menuDistance (fun j => evolvedKernel (Kernel.const (Field N μ) (ν j))
        (transitionKernel μ β T) H) (gibbsKernel μ β H) :=
    funext (physicalMenuDistance_eq_endpoint hN μ β ν T)
  rw [he]
  exact menu_endpoint_measurable _ _ _

/-- The actual distance is exactly the source joint infimum over every
simplex weight and every time, including singular initial measures. -/
theorem physicalMenuDistance_eq_joint_inf (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (ν : ι → Measure (Vector N)) [∀ j, IsProbabilityMeasure (ν j)]
    (T : ℝ≥0) (H : Field N μ) :
    physicalMenuDistance μ β ν T H =
      sInf {r : ℝ | ∃ w : Weights ι, ∃ t : ℝ≥0, t ≤ T ∧
        r = totalVariation (physicalSemigroup μ β H t ∘ₘ mixture ν w) (gibbsKernel μ β H)} := by
  apply menuAllTimeDistance_eq_joint_inf _ _ _
    (mixed_kernel_semigroup μ (coefficientLift μ H) β)
  intro t
  rw [gibbsKernel_apply]
  exact mixedTransitionKernel_gibbs_invariant hN μ (coefficientLift μ H) β t

theorem allTimeDistance_nonneg (P : ℝ≥0 → Kernel (Vector N) (Vector N))
    [∀ t, IsMarkovKernel (P t)] (ν π : Measure (Vector N))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure π] (T : ℝ≥0) :
    0 ≤ allTimeDistance P ν π T := by
  apply le_csInf
  · exact ⟨_,T,⟨zero_le,le_rfl⟩,rfl⟩
  · rintro r ⟨t,ht,rfl⟩
    exact totalVariation_nonneg _ _

theorem allTimeDistance_le_one (P : ℝ≥0 → Kernel (Vector N) (Vector N))
    [∀ t, IsMarkovKernel (P t)] (ν π : Measure (Vector N))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure π] (T : ℝ≥0) :
    allTimeDistance P ν π T ≤ 1 := by
  have hb : BddBelow ((fun t => totalVariation (P t ∘ₘ ν) π) '' Icc 0 T) :=
    ⟨0,by rintro r ⟨t,ht,rfl⟩; exact totalVariation_nonneg _ _⟩
  exact (csInf_le hb ⟨T,⟨zero_le,le_rfl⟩,rfl⟩).trans (totalVariation_le_one _ _)

section Varying
variable {ιₙ : ℕ → Type*} [∀ N, Fintype (ιₙ N)] [∀ N, Nonempty (ιₙ N)]

/-- Exact source cor:red-selection for the actual physical model,
uniformly over all convex combinations and all times in [0,T_N]. -/
theorem prescribed_menu_allTime_separation (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (ν : ∀ N, ιₙ N → Measure (Vector N)) [∀ N j, IsProbabilityMeasure (ν N j)]
    (B : ∀ N, ℝ → Set (Field N μ × Vector N)) (hB : ∀ N M, MeasurableSet (B N M))
    (hsupport : ∀ N, 2 ≤ N → ∀ j, ∀ᵐ x ∂ν N j, OnSphere x)
    (hrot : ∀ M : ℝ, 0 < M → ∀ N, 2 ≤ N →
      ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ),
      Prod.mk (fieldRotation μ U H) ⁻¹' B N M = U '' (Prod.mk H ⁻¹' B N M))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop,
        (∫ H, (gibbsKernel (N := N) μ β H).real (Prod.mk H ⁻¹' B N M)ᶜ ∂fieldLaw N μ) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto
      (fun N => (Fintype.card (ιₙ N) : ℝ)*uniformEntryMass μ β (T N) (B N M)) atTop (𝓝 0)) :
    InProbability (fun N => fieldLaw N μ)
      (fun N => physicalMenuDistance μ β (ν N) (T N)) 1 := by
  have herror (M : ℝ) (hM : 0 < M) :
      Tendsto (fun N => ∫ H, menuError (fun j => Kernel.const (Field N μ) (ν N j))
        (transitionKernel μ β (T N)) (B N M) H ∂fieldLaw N μ) atTop (𝓝 0) := by
    have he : ∀ᶠ N in atTop,
        (∫ H, menuError (fun j => Kernel.const (Field N μ) (ν N j))
          (transitionKernel μ β (T N)) (B N M) H ∂fieldLaw N μ) =
          (Fintype.card (ιₙ N) : ℝ)*uniformEntryMass μ β (T N) (B N M) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      apply prescribed_menuError_integral_eq_ae _ _ _ (hB N M)
      intro j
      filter_upwards [hsupport N hN j] with x hx
      exact point_entry_eq_uniform (by omega) μ β (T N) (hB N M)
        (pullbackBand_rotation_of_full_field μ (B N M) (hrot M hM N hN)) x hx
    exact (hsize M hM).congr' (he.mono fun _ h => h.symm)
  have hend := menu_endpoint_separation_of_capture (fun N => fieldLaw N μ)
    (fun N j => Kernel.const (Field N μ) (ν N j)) (fun N => gibbsKernel (N := N) μ β)
    (fun N => transitionKernel (N := N) μ β (T N)) B hB hcapture herror
  apply ReductionInformationEventually.inProbability_congr_eventually
    (fun N => fieldLaw N μ) _ (fun N => physicalMenuDistance μ β (ν N) (T N)) 1 _ hend
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  intro H
  exact (physicalMenuDistance_eq_endpoint hN μ β (ν N) (T N) H).symm

omit [∀ N, Nonempty (ιₙ N)] in
/-- Arbitrary field-selected weights inherit the proved uniform physical
menu conclusion. No measurability of the selected weights is needed. -/
theorem selected_weights_allTime_separation_of_uniform (μ : FiniteMixture) (β : ℝ)
    (T : ℕ → ℝ≥0) (ν : ∀ N, ιₙ N → Measure (Vector N))
    [∀ N j, IsProbabilityMeasure (ν N j)] (w : ∀ N, Field N μ → Weights (ιₙ N))
    (hmenu : InProbability (fun N => fieldLaw N μ)
      (fun N => physicalMenuDistance μ β (ν N) (T N)) 1) :
    InProbability (fun N => fieldLaw N μ)
      (fun N H => allTimeDistance (physicalSemigroup μ β H)
        (mixture (ν N) (w N H)) (gibbsKernel μ β H) (T N)) 1 := by
  apply inProbability_one_of_ge (fun N => fieldLaw N μ) _ _ hmenu
  · intro N H
    apply ciInf_le
    exact ⟨0,by rintro r ⟨v,rfl⟩; exact allTimeDistance_nonneg _ _ _ _⟩
  · intro N H
    exact allTimeDistance_le_one _ _ _ _

theorem selected_index_allTime_separation_of_uniform (μ : FiniteMixture) (β : ℝ)
    (T : ℕ → ℝ≥0) (ν : ∀ N, ιₙ N → Measure (Vector N))
    [∀ N j, IsProbabilityMeasure (ν N j)] (j : ∀ N, Field N μ → ιₙ N)
    (hmenu : InProbability (fun N => fieldLaw N μ)
      (fun N => physicalMenuDistance μ β (ν N) (T N)) 1) :
    InProbability (fun N => fieldLaw N μ)
      (fun N H => allTimeDistance (physicalSemigroup μ β H)
        (ν N (j N H)) (gibbsKernel μ β H) (T N)) 1 := by
  have hs := selected_weights_allTime_separation_of_uniform μ β T ν
    (fun N H => vertexWeights (j N H)) hmenu
  convert hs using 1
  funext N H
  rw [mixture_vertexWeights]

variable {Rₙ : ℕ → Type*} [∀ N, MeasurableSpace (Rₙ N)]

/-- The source independent-random-menu clause uses the literal product
law of menu randomness and the full polynomial H, and the same K_N q_N,M.
It is uniform over every weight, every time and every menu realization. -/
theorem independent_random_menu_allTime_separation (μ : FiniteMixture) (β : ℝ)
    (T : ℕ → ℝ≥0) (ρ : ∀ N, Measure (Rₙ N)) [∀ N, IsProbabilityMeasure (ρ N)]
    (ν : ∀ N, Rₙ N → ιₙ N → Measure (Vector N))
    (hν : ∀ N j, Measurable (fun r => ν N r j)) [∀ N r j, IsProbabilityMeasure (ν N r j)]
    (B : ∀ N, ℝ → Set (Field N μ × Vector N)) (hB : ∀ N M, MeasurableSet (B N M))
    (hsupport : ∀ N, 2 ≤ N → ∀ r j, ∀ᵐ x ∂ν N r j, OnSphere x)
    (hrot : ∀ M : ℝ, 0 < M → ∀ N, 2 ≤ N →
      ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ),
      Prod.mk (fieldRotation μ U H) ⁻¹' B N M = U '' (Prod.mk H ⁻¹' B N M))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop,
        (∫ H, (gibbsKernel (N := N) μ β H).real (Prod.mk H ⁻¹' B N M)ᶜ ∂fieldLaw N μ) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto
      (fun N => (Fintype.card (ιₙ N) : ℝ)*uniformEntryMass μ β (T N) (B N M)) atTop (𝓝 0)) :
    InProbability (fun N => (ρ N).prod (fieldLaw N μ))
      (fun N z => physicalMenuDistance μ β (ν N z.1) (T N) z.2) 1 := by
  have herror (M : ℝ) (hM : 0 < M) :
      Tendsto (fun N => ∫ z, menuError
        (randomInitial (Ω := Field N μ) (ν N) (hν N))
        (liftTransition (Rₙ N) (transitionKernel μ β (T N))) (liftBand (Rₙ N) (B N M)) z
          ∂(ρ N).prod (fieldLaw N μ)) atTop (𝓝 0) := by
    have he : ∀ᶠ N in atTop,
        (∫ z, menuError (randomInitial (Ω := Field N μ) (ν N) (hν N))
          (liftTransition (Rₙ N) (transitionKernel μ β (T N))) (liftBand (Rₙ N) (B N M)) z
            ∂(ρ N).prod (fieldLaw N μ)) =
          (Fintype.card (ιₙ N) : ℝ)*uniformEntryMass μ β (T N) (B N M) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      apply random_menuError_integral_eq_ae (ρ N) (fieldLaw N μ) (ν N) (hν N)
        (transitionKernel μ β (T N)) (hB N M)
      intro r j
      filter_upwards [hsupport N hN r j] with x hx
      exact point_entry_eq_uniform (by omega) μ β (T N) (hB N M)
        (pullbackBand_rotation_of_full_field μ (B N M) (hrot M hM N hN)) x hx
    exact (hsize M hM).congr' (he.mono fun _ h => h.symm)
  have hcap : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop,
        (∫ z : Rₙ N × Field N μ, (gibbsKernel (N := N) μ β z.2).real
          (Prod.mk z.2 ⁻¹' B N M)ᶜ ∂(ρ N).prod (fieldLaw N μ)) < η := by
    intro η hη
    obtain ⟨M,hM,hcap⟩ := hcapture η hη
    refine ⟨M,hM,?_⟩
    filter_upwards [hcap] with N hN
    rw [integral_fun_snd (μ := ρ N) (ν := fieldLaw N μ)
      (fun H => (gibbsKernel (N := N) μ β H).real (Prod.mk H ⁻¹' B N M)ᶜ),
      probReal_univ,one_smul]
    exact hN
  have hend := menu_endpoint_separation_of_capture (fun N => (ρ N).prod (fieldLaw N μ))
    (fun N => randomInitial (Ω := Field N μ) (ν N) (hν N))
    (fun N => (gibbsKernel (N := N) μ β).comap Prod.snd measurable_snd)
    (fun N => liftTransition (Rₙ N) (transitionKernel μ β (T N)))
    (fun N M => liftBand (Rₙ N) (B N M)) (fun N M => liftBand_measurable (hB N M))
    hcap herror
  apply ReductionInformationEventually.inProbability_congr_eventually
    (fun N => (ρ N).prod (fieldLaw N μ)) _
    (fun N z => physicalMenuDistance μ β (ν N z.1) (T N) z.2) 1 _ hend
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  intro z
  rw [physicalMenuDistance_eq_endpoint hN μ β (ν N z.1) (T N) z.2]
  congr 1
  funext j
  rw [evolvedKernel_apply,evolvedKernel_apply,liftTransition_conditional]
  rfl

end Varying
end
end SlowEquilibration.SphericalMenuReduction
