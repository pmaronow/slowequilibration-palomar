-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalResidualOriginalIntegral
public import SlowEquilibration.SphericalTAPCriticalLatitudeNormalization

@[expose] public section

/-! The transverse probability measure in manuscript §12 has radius `sqrt N`,
where `N = n+1`, and the physical band point is `sqrt Q • u + sqrt (1-Q) • ω`.
The earlier compact-carrier integral used the equivalent rescaled offset
`sqrt ((1-Q)/Q) • ω`. This leaf states the source-radius integral separately
and proves the change of coordinates, including its posterior lower tails. -/

namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet SphericalTaylorRemainder
open WholeFieldRegression SphericalMarkedWindows SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A point on the source transverse sphere of radius `sqrt (n+1)`, obtained
from a canonical radius-`sqrt n` sphere point through an orthogonal frame. -/
def sourceRadiusTransversePoint (n : ℕ)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (y : Vector n) : Vector (n+1) :=
  Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e y

/-- The source's `ν_u^⊥`, in an orthogonal frame. It is the uniform
probability law on the radius-`sqrt (n+1)` sphere in the tangent hyperplane. -/
def sourceRadiusTransverseLaw (n : ℕ)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) : Measure (Vector (n+1)) :=
  (sphereLaw n).map (sourceRadiusTransversePoint n e)

theorem sourceRadiusTransversePoint_continuous (n : ℕ)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) :
    Continuous (sourceRadiusTransversePoint n e) := by
  unfold sourceRadiusTransversePoint
  exact e.continuous.const_smul (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)))

theorem sourceRadiusTransverseLaw_probability (n : ℕ)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) :
    IsProbabilityMeasure (sourceRadiusTransverseLaw n e) := by
  unfold sourceRadiusTransverseLaw
  infer_instance

/-- The source-radius measure is genuinely supported on vectors with
Euclidean norm squared `N`, without a `Q`-dependent radius. -/
theorem sourceRadiusTransverseLaw_radius (n : ℕ) (hn : 1 ≤ n)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) :
    ∀ᵐ ω ∂sourceRadiusTransverseLaw n e, ‖ω‖^2=((n+1:ℕ):ℝ) := by
  unfold sourceRadiusTransverseLaw
  apply (ae_map_iff (sourceRadiusTransversePoint_continuous n e).measurable.aemeasurable
    (by measurability)).2
  filter_upwards [sphereLaw_support hn] with y hy
  have hnR : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  change ‖Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e y‖^2=_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    e.norm_map,mul_pow,Real.sq_sqrt (div_nonneg (by positivity) (by positivity)),hy]
  field_simp [hnR]

/-- Each source-radius offset lies in the tangent hyperplane of the center. -/
theorem sourceRadiusTransverseLaw_tangent (n : ℕ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ y, inner ℝ (e y) u=0) :
    ∀ᵐ ω ∂sourceRadiusTransverseLaw n e, inner ℝ ω u=0 := by
  unfold sourceRadiusTransverseLaw
  apply (ae_map_iff (sourceRadiusTransversePoint_continuous n e).measurable.aemeasurable
    (by measurability)).2
  exact Filter.Eventually.of_forall (fun y => by
    change inner ℝ (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e y) u=0
    rw [inner_smul_left,he,mul_zero])

/-- The usual latitude chart is literally the source chart applied to an
offset of radius `sqrt N`. This identity holds for every latitude. -/
theorem latitudeMap_eq_sourceRadius (n : ℕ) (hn : 1 ≤ n)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (a : ℝ) (y : Vector n) :
    latitudeMap u e a y = a • u +
      Real.sqrt (1-a^2) • sourceRadiusTransversePoint n e y := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hratio : 0 ≤ (((n+1:ℕ):ℝ)/(n:ℝ)) :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have hroot : Real.sqrt ((((n+1:ℕ):ℝ)/(n:ℝ))*(1-a^2)) =
      Real.sqrt (1-a^2)*Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) := by
    rw [Real.sqrt_mul hratio]
    ring
  unfold latitudeMap sourceRadiusTransversePoint
  rw [smul_smul,hroot]

/-- Consequently the genuine spherical latitude law uses precisely the
same radius-`sqrt N` tangent measure as the source integral. -/
theorem latitudeLaw_eq_sourceRadius_map (n : ℕ) (hn : 1 ≤ n)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (a : ℝ) :
    latitudeLaw u e a = (sourceRadiusTransverseLaw n e).map
      (fun ω => a • u + Real.sqrt (1-a^2) • ω) := by
  have hPhysical : Measurable (fun ω : Vector (n+1) =>
      a • u + Real.sqrt (1-a^2) • ω) := by fun_prop
  unfold latitudeLaw sourceRadiusTransverseLaw
  rw [Measure.map_map hPhysical
    (sourceRadiusTransversePoint_continuous n e).measurable]
  congr 1
  funext y
  exact latitudeMap_eq_sourceRadius n hn u e a y

/-- At the critical latitude the compact-carrier band point equals the
source's printed point `sqrt Q • u + sqrt (1-Q) • ω`. -/
theorem transverseBandPoint_eq_sourceRadius (n : ℕ) (hn : 1 ≤ n)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1) (y : Vector n) :
    transverseBandPoint u e Q y = Real.sqrt Q • u +
      Real.sqrt (1-Q) • sourceRadiusTransversePoint n e y := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hQone : 0<1-Q := sub_pos.mpr hQ.2
  have harg : 0 ≤ (((n+1:ℕ):ℝ)*(1-Q)/(Q*(n:ℝ))) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hQone.le)
      (mul_nonneg hQ.1.le hnR.le)
  have hratio : 0 ≤ (((n+1:ℕ):ℝ)/(n:ℝ)) :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have hleft : 0 ≤ Real.sqrt Q *
      Real.sqrt (((n+1:ℕ):ℝ)*(1-Q)/(Q*(n:ℝ))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.sqrt (1-Q)*
      Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt Q * Real.sqrt (((n+1:ℕ):ℝ)*(1-Q)/(Q*(n:ℝ))))^2 =
      (Real.sqrt (1-Q)*Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)))^2 := by
    rw [mul_pow,Real.sq_sqrt hQ.1.le,Real.sq_sqrt harg,
      mul_pow,Real.sq_sqrt (sub_nonneg.mpr hQ.2.le),Real.sq_sqrt hratio]
    field_simp [hQ.1.ne',hnR.ne']
  have hscalar : Real.sqrt Q *
      Real.sqrt (((n+1:ℕ):ℝ)*(1-Q)/(Q*(n:ℝ))) =
      Real.sqrt (1-Q)*Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) := by
    nlinarith
  unfold transverseBandPoint transverseOffset sourceRadiusTransversePoint
  rw [smul_add,smul_smul,smul_smul,hscalar]

/-- The exact normalized residual integral in the coordinates and radius
printed in manuscript Lemma 12.18. -/
def sourceRadiusCriticalResidualNormalizedPartition (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (β e₀ : ℝ)
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  Real.exp (-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2) *
    ∫ ω : Vector (n+1), Real.exp (β*(field (mixtureCoefficients μ) J
      (Real.sqrt Q • u + Real.sqrt (1-Q) • ω)-((n+1:ℕ):ℝ)*e₀))
      ∂sourceRadiusTransverseLaw n e

/-- The physical central-latitude partition in the exact source
coordinates. Its integration law has radius `sqrt N` and no `Q` scaling. -/
def sourceRadiusCriticalLatitudePartition (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (β : ℝ)
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  ∫ ω : Vector (n+1), Real.exp (β*field (mixtureCoefficients μ) J
    (Real.sqrt Q • u + Real.sqrt (1-Q) • ω)) ∂sourceRadiusTransverseLaw n e

/-- Source equation `mb-section` with the source's own radius-`sqrt N`
transverse measure and central-latitude partition. -/
theorem sourceRadiusCriticalResidualNormalizedPartition_eq_latitude
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β e₀ : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    sourceRadiusCriticalResidualNormalizedPartition n μ hQ u e β e₀ J =
      Real.exp (-(((n+1:ℕ):ℝ)*β^2*
        (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2+
          β*(((n+1:ℕ):ℝ)*e₀))) *
        sourceRadiusCriticalLatitudePartition n μ Q u e β J := by
  let A := ((n+1:ℕ):ℝ)*β^2*
    (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2
  let m := ((n+1:ℕ):ℝ)*e₀
  let H : Vector (n+1) → ℝ := fun ω =>
    field (mixtureCoefficients μ) J (Real.sqrt Q • u + Real.sqrt (1-Q) • ω)
  unfold sourceRadiusCriticalResidualNormalizedPartition sourceRadiusCriticalLatitudePartition
  dsimp only
  change Real.exp (-((n+1:ℕ):ℝ)*β^2*
      (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)*
      (∫ ω, Real.exp (β*(H ω-m)) ∂sourceRadiusTransverseLaw n e) =
    Real.exp (-(A+β*m))*
      (∫ ω, Real.exp (β*H ω) ∂sourceRadiusTransverseLaw n e)
  have he (ω : Vector (n+1)) :
      Real.exp (β*(H ω-m)) = Real.exp (-β*m)*Real.exp (β*H ω) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [he, integral_const_mul]
  rw [←mul_assoc, ←Real.exp_add]
  congr 1
  dsimp [A]
  push_cast
  ring

/-- Change of variables from the previous rescaled-offset bridge to the
literal radius-`sqrt N` source integral, pointwise in the full disorder. -/
theorem sourceRadiusCriticalResidualNormalizedPartition_eq_original (n : ℕ)
    (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β e₀ : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    sourceRadiusCriticalResidualNormalizedPartition n μ hQ u e β e₀ J =
      originalCriticalTransverseNormalizedPartition n μ hQ u e β e₀ J := by
  let F : Vector (n+1) → ℝ := fun ω =>
    Real.exp (β*(field (mixtureCoefficients μ) J
      (Real.sqrt Q • u + Real.sqrt (1-Q) • ω)-((n+1:ℕ):ℝ)*e₀))
  let G : Vector (n+1) → ℝ := fun ω =>
    Real.exp (β*(field (mixtureCoefficients μ) J
      (Real.sqrt Q • (u+ω))-((n+1:ℕ):ℝ)*e₀))
  have hF : Measurable F := by
    dsimp only [F]
    have hOffset : Continuous (fun ω : Vector (n+1) => Real.sqrt (1-Q) • ω) :=
      by fun_prop
    have hArgument : Continuous (fun ω : Vector (n+1) =>
        field (mixtureCoefficients μ) J
          (Real.sqrt Q • u+Real.sqrt (1-Q) • ω)-((n+1:ℕ):ℝ)*e₀) :=
      ((field_contDiff (mixtureCoefficients μ) J).continuous.comp
        (continuous_const.add hOffset)).sub continuous_const
    exact (Real.continuous_exp.comp (hArgument.const_mul β)).measurable
  have hG : Measurable G := by
    dsimp only [G]
    have hArgument : Continuous (fun ω : Vector (n+1) =>
        field (mixtureCoefficients μ) J
          (Real.sqrt Q • (u+ω))-((n+1:ℕ):ℝ)*e₀) :=
      ((field_contDiff (mixtureCoefficients μ) J).continuous.comp
        ((continuous_const.add continuous_id).const_smul (Real.sqrt Q))).sub continuous_const
    exact (Real.continuous_exp.comp (hArgument.const_mul β)).measurable
  have hSource :
      (∫ ω, F ω ∂sourceRadiusTransverseLaw n e) =
        ∫ y : Vector n, F (sourceRadiusTransversePoint n e y) ∂sphereLaw n := by
    exact integral_map (sourceRadiusTransversePoint_continuous n e).measurable.aemeasurable
      hF.aestronglyMeasurable
  have hOld :
      (∫ ω, G ω ∂criticalTransverseOffsetLaw n Q e) =
        ∫ y : Vector n, G (transverseOffset e Q y) ∂sphereLaw n := by
    exact integral_map (transverseOffset_parameter_continuous e Q _ continuous_id).measurable.aemeasurable
      hG.aestronglyMeasurable
  unfold sourceRadiusCriticalResidualNormalizedPartition
    originalCriticalTransverseNormalizedPartition
  dsimp only
  change _ * (∫ ω, F ω ∂sourceRadiusTransverseLaw n e) =
    _ * (∫ ω, G ω ∂criticalTransverseOffsetLaw n Q e)
  rw [hSource,hOld]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change Real.exp (β*(field (mixtureCoefficients μ) J
        (Real.sqrt Q • u + Real.sqrt (1-Q) • sourceRadiusTransversePoint n e y)-
          ((n+1:ℕ):ℝ)*e₀)) =
      Real.exp (β*(field (mixtureCoefficients μ) J
        (Real.sqrt Q • (u+transverseOffset e Q y))-
          ((n+1:ℕ):ℝ)*e₀))
    rw [← transverseBandPoint_eq_sourceRadius n hn u e hQ y]
    rfl)

/-- The central latitude integral itself is unchanged by the offset
rescaling, so both full-width and central computations use one observable. -/
theorem sourceRadiusCriticalLatitudePartition_eq_original (n : ℕ)
    (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    sourceRadiusCriticalLatitudePartition n μ Q u e β J =
      originalCriticalLatitudePartition n μ Q u e β J := by
  have h := sourceRadiusCriticalResidualNormalizedPartition_eq_original
    n hn μ hQ u e β 0 J
  rw [sourceRadiusCriticalResidualNormalizedPartition_eq_latitude,
    originalCriticalTransverseNormalizedPartition_eq_latitude] at h
  have h' : Real.exp (-(((n+1:ℕ):ℝ)*β^2*
      (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)) *
        sourceRadiusCriticalLatitudePartition n μ Q u e β J =
      Real.exp (-(((n+1:ℕ):ℝ)*β^2*
      (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)) *
        originalCriticalLatitudePartition n μ Q u e β J := by
    simpa only [mul_zero,add_zero] using h
  exact mul_left_cancel₀ (Real.exp_ne_zero _) h'

/-- Direct identification of the actual compact-carrier observable with the
printed radius-`sqrt N` integral, with no abstract partition surrogate. -/
theorem actualCriticalResidualNormalizedPartition_eq_sourceRadius (n : ℕ)
    (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β e₀ : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    actualCriticalResidualNormalizedPartition n μ hQ u e β e₀ J =
      sourceRadiusCriticalResidualNormalizedPartition n μ hQ u e β e₀ J :=
  (actualCriticalResidualNormalizedPartition_eq_original_integral
    n hn μ hQ u e β e₀ J).trans
    (sourceRadiusCriticalResidualNormalizedPartition_eq_original
      n hn μ hQ u e β e₀ J).symm

/-- Source Lemma 12.18, now with precisely the printed `ν_u^⊥` radius and
band argument, under the value-conditioned one-point law. -/
theorem sourceRadius_value_critical_partition_lower_tail (μ : FiniteMixture)
    {β x Q : ℝ} (h : Certificate μ β x Q) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
        (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ y,inner ℝ (e y) u=0)
        (e₀ : ℝ),
      (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀).real
        {J | sourceRadiusCriticalResidualNormalizedPartition n μ h.overlap_range
          u e β e₀ J < t} ≤ ε := by
  intro ε hε
  obtain ⟨t,ht,hTail⟩ := original_value_critical_transverse_partition_lower_tail μ h ε hε
  refine ⟨t,ht,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he e₀
  simpa only [sourceRadiusCriticalResidualNormalizedPartition_eq_original n hdim μ
    h.overlap_range u e β e₀] using hn u hu e he e₀

/-- The same source-radius lower tail under the mixed value/radial-score
posterior, uniformly in the two mark coordinates. -/
theorem sourceRadius_mixed_critical_partition_lower_tail (μ : FiniteMixture)
    {β x Q : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
        (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ y,inner ℝ (e y) u=0)
        (b : EuclideanSpace ℝ (Fin 2)),
      (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).real
        {J | sourceRadiusCriticalResidualNormalizedPartition n μ h.overlap_range
          u e β (b 0) J < t} ≤ ε := by
  intro ε hε
  obtain ⟨t,ht,hTail⟩ := original_mixed_critical_transverse_partition_lower_tail μ h hnp ε hε
  refine ⟨t,ht,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he b
  simpa only [sourceRadiusCriticalResidualNormalizedPartition_eq_original n hdim μ
    h.overlap_range u e β (b 0)] using hn u hu e he b

end
end SlowEquilibration.SphericalTAPCriticalBand
