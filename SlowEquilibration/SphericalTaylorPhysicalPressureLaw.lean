-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorPosteriorPartitionLaw
public import SlowEquilibration.SphericalTaylorBandPartition
public import SlowEquilibration.CompactSphereCarrier

@[expose] public section

/-! The exact law of the literal physical transverse residual pressure under
every genuine first-jet posterior, against the actual uniform sphere law. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphericalLatitudeChartKacRice
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_posterior_transverseRemainderPressure_map {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : Q∈Set.Ioo (0 : ℝ) 1) (β : ℝ)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ y,inner ℝ (e y) w=0)
    {q : ℝ} (hq : |q|≤1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (coefficientKernel (latitudeJointCLM c w e q y hy) target).map
      (fun J => transverseRemainderPressure c w e q Q β J y)=
    (disorderLaw n θ.maxDegree).map
      (fun J => Real.log (partition n (β*Real.sqrt (((n+2 : ℕ) : ℝ)/(n : ℝ)))
        (fieldOfMixture θ J))/((n+2 : ℕ) : ℝ)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  let l := bottomTransverseFrame e y
  let z := fun u : CompactSphereCarrier.Carrier n => transverseOffset l Q (u : Vector n)
  have hz : Continuous z := transverseOffset_parameter_continuous l Q Subtype.val continuous_subtype_val
  let : IsProbabilityMeasure (CompactSphereCarrier.law n) := CompactSphereCarrier.law_probability hn
  have hl : ∀ v,inner ℝ (l v) (latitudeMap w e q y)=0 :=
    bottomTransverseFrame_center_orthogonal w e he q y hy
  have hLaw := latitude_posterior_transverse_logPartition_law (by omega : 0<n)
    (CompactSphereCarrier.law n) β μ hQ w hw e he hq y hy l hl
      (Subtype.val : CompactSphereCarrier.Carrier n → Vector n) continuous_subtype_val target
  have hleft (J : Disorder (n+2) μ.maxDegree) :
      ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β
        (taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J))/((n+2 : ℕ) : ℝ)=
      transverseRemainderPressure c w e q Q β J y := by
    have hc := transverseRemainderField_continuous c w e q Q J y
    have heq : taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J)=
        (⟨fun u : CompactSphereCarrier.Carrier n => transverseRemainderField c w e q Q J y u,
          hc.comp continuous_subtype_val⟩ : C(CompactSphereCarrier.Carrier n,ℝ)) := by
      ext u
      rfl
    rw [heq,CompactSphereCarrier.logPartition_eq_sphere hn β _ hc]
    rfl
  have hright (J : Disorder n θ.maxDegree) :
      ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n)
        (β*Real.sqrt (((n+2 : ℕ) : ℝ)/(n : ℝ)))
        (modelContinuousField (mixtureCoefficients θ) Subtype.val continuous_subtype_val (euclideanDisorder J))/
          ((n+2 : ℕ) : ℝ)=
      Real.log (partition n (β*Real.sqrt (((n+2 : ℕ) : ℝ)/(n : ℝ))) (fieldOfMixture θ J))/((n+2 : ℕ) : ℝ) := by
    have hc : Continuous (fieldOfMixture θ J) := (field_contDiff (mixtureCoefficients θ) J).continuous
    have heq : modelContinuousField (mixtureCoefficients θ) Subtype.val continuous_subtype_val (euclideanDisorder J)=
        (⟨fun u : CompactSphereCarrier.Carrier n => fieldOfMixture θ J u,hc.comp continuous_subtype_val⟩ :
          C(CompactSphereCarrier.Carrier n,ℝ)) := by
      ext u
      exact valueObservation_actual _ _ _
    rw [heq,CompactSphereCarrier.logPartition_eq_sphere hn _ _ hc]
    rfl
  simp only [c,θ,z,l] at hleft hright
  simpa only [hleft,hright,l] using hLaw

end
end SlowEquilibration.SphericalTaylorRemainder
