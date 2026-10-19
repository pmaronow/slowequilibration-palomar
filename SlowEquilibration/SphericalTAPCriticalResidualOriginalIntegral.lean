-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalResidualPartition

@[expose] public section

/-! An explicit measure-level bridge from the compact-carrier implementation
of the critical residual partition to the manuscript's physical transverse
sphere integral. The transverse offset law is the pushforward of the actual
normalized sphere law by the orthogonal frame and its physical radius. -/

namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet SphericalTaylorRemainder
open WholeFieldRegression SphericalMarkedWindows
open SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's framed normalized transverse measure `ν_u^⊥` on the
physical offsets `ω` for `σ = sqrt(Q) (u + ω)`. -/
def criticalTransverseOffsetLaw (n : ℕ) (Q : ℝ)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) : Measure (Vector (n+1)) :=
  (sphereLaw n).map (transverseOffset e Q)

/-- Literal `L_N^res` written on the original tangent sphere with the
original Hamiltonian and the actual one-point conditioned value mark. -/
def originalCriticalTransverseNormalizedPartition (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (β e₀ : ℝ)
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  Real.exp (-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2) *
    ∫ ω : Vector (n+1),
      Real.exp (β*(field (mixtureCoefficients μ) J
        (Real.sqrt Q • (u+ω))-((n+1:ℕ):ℝ)*e₀))
        ∂criticalTransverseOffsetLaw n Q e

/-- The positive normalized partition used by the proved posterior lower
tail is exactly the manuscript's `ν_u^⊥` integral, pointwise in disorder. -/
theorem actualCriticalResidualNormalizedPartition_eq_original_integral
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (β e₀ : ℝ)
    (J : Disorder (n+1) μ.maxDegree) :
    actualCriticalResidualNormalizedPartition n μ hQ u e β e₀ J =
      originalCriticalTransverseNormalizedPartition n μ hQ u e β e₀ J := by
  let H : Vector n → ℝ := fun y =>
    field (mixtureCoefficients μ) J (transverseBandPoint u e Q y)-((n+1:ℕ):ℝ)*e₀
  have hOffset : Continuous (transverseOffset e Q : Vector n → Vector (n+1)) :=
    transverseOffset_parameter_continuous e Q _ continuous_id
  have hH : Continuous H := by
    dsimp only [H, transverseBandPoint]
    exact ((field_contDiff (mixtureCoefficients μ) J).continuous.comp
      ((continuous_const.add hOffset).const_smul (Real.sqrt Q))).sub continuous_const
  have hCarrier :
      actualCriticalBandContinuousField n n μ Q u e
        (fun x : CompactSphereCarrier.Carrier n => x.val) continuous_subtype_val
          (euclideanDisorder J) -
          ContinuousMap.const (CompactSphereCarrier.Carrier n) ((n+1:ℕ)*e₀) =
      ⟨fun y : CompactSphereCarrier.Carrier n => H y.val,
        hH.comp continuous_subtype_val⟩ := by
    ext y
    rw [ContinuousMap.sub_apply, actualCriticalBandContinuousField_apply]
    rfl
  have hCarrierInt :
      ContinuousFieldPartition.partition (CompactSphereCarrier.law n) β
        (actualCriticalBandContinuousField n n μ Q u e
          (fun x : CompactSphereCarrier.Carrier n => x.val) continuous_subtype_val
            (euclideanDisorder J) -
            ContinuousMap.const (CompactSphereCarrier.Carrier n) ((n+1:ℕ)*e₀)) =
        ∫ y : Vector n, Real.exp (β*H y) ∂sphereLaw n := by
    unfold ContinuousFieldPartition.partition
    rw [hCarrier]
    exact CompactSphereCarrier.integral_coe hn _
      (Real.continuous_exp.comp (hH.const_mul β)).measurable
  let F : Vector (n+1) → ℝ := fun ω =>
    Real.exp (β*(field (mixtureCoefficients μ) J
      (Real.sqrt Q • (u+ω))-((n+1:ℕ):ℝ)*e₀))
  have hArgument : Continuous (fun ω : Vector (n+1) =>
      field (mixtureCoefficients μ) J (Real.sqrt Q • (u+ω))-
        ((n+1:ℕ):ℝ)*e₀) :=
    ((field_contDiff (mixtureCoefficients μ) J).continuous.comp
      ((continuous_const.add continuous_id).const_smul (Real.sqrt Q))).sub continuous_const
  have hF : Measurable F := by
    dsimp only [F]
    exact (Real.continuous_exp.comp (hArgument.const_mul β)).measurable
  have hTransport :
      (∫ ω : Vector (n+1), F ω ∂criticalTransverseOffsetLaw n Q e) =
        ∫ y : Vector n, Real.exp (β*H y) ∂sphereLaw n := by
    rw [criticalTransverseOffsetLaw, integral_map hOffset.measurable.aemeasurable
      hF.aestronglyMeasurable]
    rfl
  rw [actualCriticalResidualNormalizedPartition_eq_partition n hn μ hQ u e β e₀ J]
  unfold originalCriticalTransverseNormalizedPartition
  dsimp only
  rw [hCarrierInt]
  exact congrArg (fun z : ℝ =>
    Real.exp (-((n+1:ℕ):ℝ)*β^2*
      (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)*z) hTransport.symm

/-- The printed Lemma 12.18 lower tail for the literal transverse integral
under the proper value-only one-point law. -/
theorem original_value_critical_transverse_partition_lower_tail (μ : FiniteMixture)
    {β x Q : ℝ} (h : Certificate μ β x Q) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
        (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ y,inner ℝ (e y) u=0)
        (e₀ : ℝ),
      (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀).real
        {J | originalCriticalTransverseNormalizedPartition n μ h.overlap_range
          u e β e₀ J < t} ≤ ε := by
  intro ε hε
  obtain ⟨t,ht,hTail⟩ := actual_value_critical_residual_partition_lower_tail μ h ε hε
  refine ⟨t,ht,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he e₀
  simpa only [← actualCriticalResidualNormalizedPartition_eq_original_integral n hdim μ
    h.overlap_range u e β e₀] using hn u hu e he e₀

/-- The same literal source lower tail under the genuine mixed one-point
energy/radial-score posterior, uniformly in both marks. -/
theorem original_mixed_critical_transverse_partition_lower_tail (μ : FiniteMixture)
    {β x Q : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
        (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ y,inner ℝ (e y) u=0)
        (b : EuclideanSpace ℝ (Fin 2)),
      (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).real
        {J | originalCriticalTransverseNormalizedPartition n μ h.overlap_range
          u e β (b 0) J < t} ≤ ε := by
  intro ε hε
  obtain ⟨t,ht,hTail⟩ := actual_mixed_critical_residual_partition_lower_tail μ h hnp ε hε
  refine ⟨t,ht,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he b
  simpa only [← actualCriticalResidualNormalizedPartition_eq_original_integral n hdim μ
    h.overlap_range u e β (b 0)] using hn u hu e he b

end
end SlowEquilibration.SphericalTAPCriticalBand
