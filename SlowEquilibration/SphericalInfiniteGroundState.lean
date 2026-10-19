-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGroundStateUnitary
public import SlowEquilibration.SphericalInfiniteOperators

/-! The ground-state transform for the actual infinite tensor field under
its original Gibbs law, on the proved probability-one C² event. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory Filter Set SphericalModel SphericalForm
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace LawTransport
theorem isometry_vector_symm {X : Type*} [MeasurableSpace X]
    {ν η : Measure X} (h : ν=η) (u : Lp ℝ 2 η) :
    isometry h (vector h.symm u) = u := by cases h; rfl

theorem vector_coe {X : Type*} [MeasurableSpace X]
    {ν η : Measure X} (h : ν=η) (u : Lp ℝ 2 ν) :
    vector h u =ᵐ[η] u := by cases h; exact .rfl
end LawTransport

/-- Literal original-series Gibbs L², unitarily mapped to uniform sphere L². -/
def literalGroundStateUnitary (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    LiteralGibbsL2 n μ J β ≃ₗᵢ[ℝ] Lp ℝ 2 (sphereLaw (n+1)) :=
  PositiveDensityL2.unitary (sphereLaw (n+1)) (gibbsLaw (n+1) β (field μ J))
    (groundStateWeight (n+1) β (regularAmbientField n μ J))
    (groundStateWeight_continuous β (regularAmbientField_contDiff n μ J).continuous).measurable
    (groundStateWeight_pos (by omega) β (regularAmbientField_contDiff n μ J).continuous)
    ((literal_gibbsLaw_eq_regular n μ β J hJ).trans
      (gibbsLaw_eq_groundStateDensity (by omega) β (regularAmbientField_contDiff n μ J).continuous))

theorem literalGroundStateUnitary_regular_coe (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (u : LiteralGibbsL2 n μ J β) :
    literalGroundStateUnitary n μ J hJ β u =ᵐ[sphereLaw (n+1)]
      (fun x => groundStateWeight (n+1) β (regularAmbientField n μ J) x * u x) :=
  PositiveDensityL2.unitary_coe _ _ _ _ _ _ u

theorem literalGroundStateUnitary_transported (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (u : Lp ℝ 2 (gibbsLaw (n+1) β (regularAmbientField n μ J))) :
    literalGroundStateUnitary n μ J hJ β
      (LawTransport.vector (literal_gibbsLaw_eq_regular n μ β J hJ).symm u) =
      groundStateUnitary (by omega) β (regularAmbientField n μ J)
        (regularAmbientField_contDiff n μ J).continuous u := by
  apply Lp.ext
  have hac := PositiveDensityL2.reverse_absolutelyContinuous (sphereLaw (n+1))
    (gibbsLaw (n+1) β (field μ J))
    (groundStateWeight (n+1) β (regularAmbientField n μ J))
    (groundStateWeight_continuous β (regularAmbientField_contDiff n μ J).continuous).measurable
    (groundStateWeight_pos (by omega) β (regularAmbientField_contDiff n μ J).continuous)
    ((literal_gibbsLaw_eq_regular n μ β J hJ).trans
      (gibbsLaw_eq_groundStateDensity (by omega) β (regularAmbientField_contDiff n μ J).continuous))
  filter_upwards [literalGroundStateUnitary_regular_coe n μ J hJ β
      (LawTransport.vector (literal_gibbsLaw_eq_regular n μ β J hJ).symm u),
    groundStateUnitary_coe (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous u,
    (LawTransport.vector_coe (literal_gibbsLaw_eq_regular n μ β J hJ).symm u).filter_mono hac.ae_le]
    with x hx hy hu
  rw [hx,hy,hu]



/-- The unitary is literally multiplication by the square root of the
original infinite-series Gibbs density, almost everywhere on the sphere. -/
theorem literalGroundStateUnitary_coe (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (u : LiteralGibbsL2 n μ J β) :
    literalGroundStateUnitary n μ J hJ β u =ᵐ[sphereLaw (n+1)]
      (fun x => Real.exp (β / 2 * field μ J x) /
        Real.sqrt (partition (n+1) β (field μ J)) * u x) := by
  filter_upwards [literalGroundStateUnitary_regular_coe n μ J hJ β u,
    sphereLaw_support (show 1≤n+1 by omega)] with x hx hs
  rw [hx,groundStateWeight,regularAmbientField_restrict n μ J hJ x hs,
    ← literal_partition_eq_regular n μ β J hJ]



/-- The Schrödinger potential is continuous and bounded for every regular
representative; on the full-measure jet event it represents the original field. -/
theorem infiniteGroundStatePotential_regular (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (β : ℝ) :
    Continuous (groundStatePotential (n+1) β (regularAmbientField n μ J)) ∧
      ∃ C : ℝ, ∀ x, SphericalAging.HardSphereDynamics.OnSphere x →
        |groundStatePotential (n+1) β (regularAmbientField n μ J) x| ≤ C :=
  ⟨groundStatePotential_continuous β (regularAmbientField_contDiff n μ J),
    groundStatePotential_bounded β (regularAmbientField_contDiff n μ J)⟩


/-- The literal original-Gibbs weak generator has the genuine C²
Schrödinger action under the actual ground-state unitary. -/
theorem literalWeakGenerator_groundState_C2 (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ u : LiteralGibbsL2 n μ J β,
      literalGroundStateUnitary n μ J hJ β u = groundSphereToL2 (by omega) f hf.continuous ∧
      ∃ hu : u∈(literalWeakGenerator n μ J hJ β).domain,
        literalGroundStateUnitary n μ J hJ β (literalWeakGenerator n μ J hJ β ⟨u,hu⟩) =
          groundSphereToL2 (by omega)
            (fun x => -rotationLaplacian (n+1) f x +
              groundStatePotential (n+1) β (regularAmbientField n μ J) x * f x)
            ((rotationLaplacian_continuous hf).neg.add
              ((groundStatePotential_continuous β (regularAmbientField_contDiff n μ J)).mul
                hf.continuous)) := by
  let U := groundStateUnitary (show 1≤n+1 by omega) β (regularAmbientField n μ J)
    (regularAmbientField_contDiff n μ J).continuous
  let A := sphericalGenerator (show 1≤n+1 by omega) β (regularAmbientField n μ J)
    (regularAmbientField_contDiff n μ J).continuous
  let v := U.symm (groundSphereToL2 (show 1≤n+1 by omega) f hf.continuous)
  obtain ⟨hv,hAv⟩ := sphericalGenerator_groundState_C2 (show 1≤n+1 by omega) β
    (regularAmbientField n μ J) (regularAmbientField_contDiff n μ J) f hf
  have ht := LawTransport.pmap_action (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    A v (A ⟨v,hv⟩) ⟨hv,rfl⟩
  obtain ⟨hu,hAu⟩ := ht
  refine ⟨LawTransport.vector (literal_gibbsLaw_eq_regular n μ β J hJ).symm v,?_,hu,?_⟩
  · rw [literalGroundStateUnitary_transported]
    exact U.apply_symm_apply _
  · change literalGroundStateUnitary n μ J hJ β
      (LawTransport.pmap (literal_gibbsLaw_eq_regular n μ β J hJ).symm A
        ⟨LawTransport.vector (literal_gibbsLaw_eq_regular n μ β J hJ).symm v,hu⟩) = _
    rw [hAu,literalGroundStateUnitary_transported]
    exact hAv


theorem literal_groundState_C2_ae (n : ℕ) (μ : InfiniteMixture) (β : ℝ) :
    ∀ᵐ J ∂disorderLaw (n+1), ∃ hJ : J∈summableJetDisorder μ,
      ∀ (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f),
        ∃ u : LiteralGibbsL2 n μ J β,
          literalGroundStateUnitary n μ J hJ β u = groundSphereToL2 (by omega) f hf.continuous ∧
          u∈(literalWeakGenerator n μ J hJ β).domain := by
  filter_upwards [summableJetDisorder_ae (by omega : 0<n+1) μ] with J hJ
  refine ⟨hJ,fun f hf => ?_⟩
  obtain ⟨u,hu,hd,_⟩ := literalWeakGenerator_groundState_C2 n μ J hJ β f hf
  exact ⟨u,hu,hd⟩

end SlowEquilibration.SphericalInfiniteModel
