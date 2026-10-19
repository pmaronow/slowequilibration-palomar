-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteIntrinsic

/-! The literal series Gibbs probability is the same as the Gibbs law used
by the actual infinite-field form and spectrum, on the proved regular event. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel SphericalIntrinsicExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem regularAmbientField_restrict (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (x : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℕ)) : regularAmbientField n μ J x=field μ J x := by
  change regularAmbientField n μ J (⟨x,hx⟩ : RoundSphere n)=_
  rw [regularAmbientField,if_pos hJ,ambientExtension_restrict]
  rfl

theorem literal_partition_eq_regular (n : ℕ) (μ : InfiniteMixture) (β : ℝ)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) :
    partition (n+1) β (field μ J)=partition (n+1) β (regularAmbientField n μ J) :=
  partition_eq_of_agree_on_sphere (by omega) β _ _
    (fun x hx => (regularAmbientField_restrict n μ J hJ x hx).symm)

theorem literal_partition_pos (n : ℕ) (μ : InfiniteMixture) (β : ℝ)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) :
    0<partition (n+1) β (field μ J) := by
  rw [literal_partition_eq_regular n μ β J hJ]
  exact partition_pos (by omega) β (regularAmbientField_contDiff n μ J).continuous

theorem literal_gibbsLaw_eq_regular (n : ℕ) (μ : InfiniteMixture) (β : ℝ)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) :
    gibbsLaw (n+1) β (field μ J)=gibbsLaw (n+1) β (regularAmbientField n μ J) :=
  gibbsLaw_eq_of_agree_on_sphere (by omega) β _ _
    (fun x hx => (regularAmbientField_restrict n μ J hJ x hx).symm)

theorem literal_gibbsLaw_eq_intrinsic (n : ℕ) (μ : InfiniteMixture) (β : ℝ)
    (J : Disorder (n+1)) :
    gibbsLaw (n+1) β (field μ J)=intrinsicGibbsLaw n β (intrinsicField n μ J) :=
  (intrinsicGibbsLaw_eq_of_extension n β (intrinsicField n μ J) (field μ J) (fun _ => rfl)).symm

theorem literal_gibbsLaw_probability (n : ℕ) (μ : InfiniteMixture) (β : ℝ)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) :
    IsProbabilityMeasure (gibbsLaw (n+1) β (field μ J)) := by
  rw [literal_gibbsLaw_eq_regular n μ β J hJ]
  exact gibbsLaw_probability (by omega) β (regularAmbientField_contDiff n μ J).continuous

theorem literal_gibbsLaw_probability_ae (n : ℕ) (μ : InfiniteMixture) (β : ℝ) :
    ∀ᵐ J ∂disorderLaw (n+1),IsProbabilityMeasure (gibbsLaw (n+1) β (field μ J)) := by
  filter_upwards [summableJetDisorder_ae (by omega : 0<n+1) μ] with J hJ
  exact literal_gibbsLaw_probability n μ β J hJ

end SlowEquilibration.SphericalInfiniteModel
