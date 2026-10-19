-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPosteriorBandLower
public import SlowEquilibration.SphericalTAPCriticalLatitudeNormalization
public import SlowEquilibration.SphericalTAPCriticalResidualSourceRadius

@[expose] public section

/-! The central latitude section in the physical band lower bound is
literally the source-radius transverse partition used in the proved
residual lower tail, under the same conditioned Hamiltonian. -/

namespace SlowEquilibration.SphericalTAPCriticalBandSectionBridge
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalTAPCriticalBand
open SlowEquilibration.SphericalTAPPosteriorBandLower
open SlowEquilibration.SphericalTAPPosteriorLatitudeRegularity
open SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression
set_option maxHeartbeats 1000000
open SlowEquilibration.SphericalTaylorRemainder
set_option autoImplicit false

/-- The critical latitude chart and original conditioned residual offset
chart specify exactly the same point of the ambient sphere. -/
theorem latitudeMap_eq_criticalTransverseOffset
    (n : ℕ) (hn : 1 ≤ n)
    (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (x : Vector n) :
    latitudeMap u e (Real.sqrt Q) x =
      Real.sqrt Q • (u + transverseOffset e Q x) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have harg : 0 ≤ (((n+1:ℕ):ℝ)*(1-Q)/(Q*(n:ℝ))) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hQ.2.le))
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
  unfold latitudeMap transverseOffset
  rw [smul_add,smul_smul,Real.sq_sqrt hQ.1.le]
  rw [Real.sqrt_mul hratio]
  rw [hscalar]
  rw [mul_comm (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ))) (Real.sqrt (1-Q))]

/-- Exact measure-level identification of the central latitude partition
with the original conditioned transverse section. -/
theorem centralLatitudePartition_eq_original
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    partitionAgainst (latitudeLaw u e (Real.sqrt Q)) β
      (field (mixtureCoefficients μ) J) =
      originalCriticalLatitudePartition n μ Q u e β J := by
  have hmap : Continuous (transverseOffset e Q : Vector n → Vector (n+1)) := by
    unfold transverseOffset
    fun_prop
  have hF : Continuous (fun ω : Vector (n+1) =>
      Real.exp (β*field (mixtureCoefficients μ) J
        (Real.sqrt Q • (u+ω)))) := by
    have hf := (field_contDiff (mixtureCoefficients μ) J).continuous
    fun_prop
  rw [latitudePartition_eq_sphereIntegral]
  unfold originalCriticalLatitudePartition criticalTransverseOffsetLaw
  rw [integral_map hmap.measurable.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp
    rw [latitudeMap_eq_criticalTransverseOffset n hn u e hQ x])

/-- The same central section in the source's radius-`√N` transverse law. -/
theorem centralLatitudePartition_eq_sourceRadius
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    partitionAgainst (latitudeLaw u e (Real.sqrt Q)) β
      (field (mixtureCoefficients μ) J) =
      sourceRadiusCriticalLatitudePartition n μ Q u e β J := by
  rw [centralLatitudePartition_eq_original n hn μ hQ u e β J]
  exact (sourceRadiusCriticalLatitudePartition_eq_original n hn μ hQ u e β J).symm

/-- The central spherical latitude section is exactly the conditioned
center and annealed factors times the manuscript's normalized residual
partition, with the source radius-`√N` transverse law. -/
theorem centralLatitudePartition_eq_sourceResidual
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β e₀ : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    partitionAgainst (latitudeLaw u e (Real.sqrt Q)) β
      (field (mixtureCoefficients μ) J) =
      Real.exp ((((n+1:ℕ):ℝ)*β^2*
        (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2+
          β*(((n+1:ℕ):ℝ)*e₀))) *
        sourceRadiusCriticalResidualNormalizedPartition n μ hQ u e β e₀ J := by
  let A : ℝ := (((n+1:ℕ):ℝ)*β^2*
    (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2+
      β*(((n+1:ℕ):ℝ)*e₀))
  have hsection := centralLatitudePartition_eq_sourceRadius n hn μ hQ u e β J
  have hres := sourceRadiusCriticalResidualNormalizedPartition_eq_latitude
    n μ hQ u e β e₀ J
  rw [← hsection] at hres
  change _ = Real.exp (-A) * _ at hres
  have hprod : Real.exp A * Real.exp (-A) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ = 1 * partitionAgainst (latitudeLaw u e (Real.sqrt Q)) β
          (field (mixtureCoefficients μ) J) := by ring
    _ = (Real.exp A * Real.exp (-A)) *
          partitionAgainst (latitudeLaw u e (Real.sqrt Q)) β
            (field (mixtureCoefficients μ) J) := by rw [hprod]
    _ = Real.exp A * sourceRadiusCriticalResidualNormalizedPartition
          n μ hQ u e β e₀ J := by rw [hres]; ring

/-- The manuscript's exact common band scale `D_N`, with `N = n+1`,
`s = 1-Q`, and `ψ_Q(1)` represented by the residual covariance. -/
def sourceCriticalBandScale (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1) (β mN : ℝ) : ℝ :=
  Real.exp (β*mN) *
    ((latitudeNormalization n).toReal / Real.sqrt (((n+1:ℕ):ℝ))) *
    (1-Q)^((((n-2:ℕ):ℝ))/2) *
    Real.exp ((((n+1:ℕ):ℝ)*β^2*
      (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2))

theorem sourceCriticalBandScale_pos (n : ℕ) (hn : 2 ≤ n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (β mN : ℝ) : 0 < sourceCriticalBandScale n μ hQ β mN := by
  unfold sourceCriticalBandScale
  have hlat : 0 < (latitudeNormalization n).toReal := by
    linarith [latitudeNormalization_toReal_ge_quarter hn]
  have hN : 0 < Real.sqrt (((n+1:ℕ):ℝ)) := by
    exact Real.sqrt_pos.mpr (by positivity)
  exact mul_pos (mul_pos
    (mul_pos (Real.exp_pos _) (div_pos hlat hN))
      (Real.rpow_pos_of_pos (sub_pos.mpr hQ.2) _)) (Real.exp_pos _)

/-- The source band scale and exact central residual normalization cancel
all mark and annealed factors in the physical latitude lower bound. -/
theorem sourceBand_lower_in_sourceResidual_scale
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (J : Disorder (n+1) μ.maxDegree)
    (I : Set ℝ) {r β C : ℝ} (e₀ mN : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hI : I ⊆ Icc (-r) r)
    (hband : Icc
      (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
      (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I)
    (hreg : ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ y, inner ℝ (e y) u = 0) →
      ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
      ∀ a ∈ Icc (-r) r,
      |iteratedDeriv 2
        (fun t => field (mixtureCoefficients μ) J
          (latitudeMap u e t x)) a| ≤ C*((n+1:ℕ):ℝ)) :
    (2 * Real.exp (-(β*C+2/(1-r^2)^2)/2)) *
      (sourceCriticalBandScale n μ hQ β mN *
        Real.exp (β*(((n+1:ℕ):ℝ)*e₀-mN)) *
        sourceRadiusCriticalResidualNormalizedPartition n μ hQ u
          (latitudeFrameAt u) β e₀ J) ≤
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) := by
  have hsource := sourceBand_lower_of_latitudeRegularity n hn μ u hu J I
    hQ.1 hr0 hr1 hβ hC hI hband hreg
  rw [centralLatitudePartition_eq_sourceResidual n (by omega) μ hQ u
    (latitudeFrameAt u) β e₀ J] at hsource
  have hExp : Real.exp (β*mN) *
      Real.exp (β*(((n+1:ℕ):ℝ)*e₀-mN)) *
      Real.exp ((((n+1:ℕ):ℝ)*β^2*
        (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)) =
      Real.exp ((((n+1:ℕ):ℝ)*β^2*
        (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2+
          β*(((n+1:ℕ):ℝ)*e₀))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  convert hsource using 1
  unfold sourceCriticalBandScale
  rw [div_eq_mul_inv]
  rw [div_eq_mul_inv]
  rw [← hExp]
  ring

/-- Exact nonpure critical-point conditioning supplies an exponentially
reliable regularity event on which the printed `D_N` comparison holds. -/
theorem mixedConditioned_sourceBand_residual_comparison
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
      ∀ mN : ℝ,
      let good := sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K
      MeasurableSet good ∧
      (mixedConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu
        (WithLp.toLp 2 ![h,k])).real goodᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((n+1:ℕ):ℝ)/2) ∧
      ∀ J ∈ good,
        (2 * Real.exp (-(β*C+2/(1-r^2)^2)/2)) *
          (sourceCriticalBandScale n μ hQ β mN *
            Real.exp (β*(((n+1:ℕ):ℝ)*h-mN)) *
            sourceRadiusCriticalResidualNormalizedPartition n μ hQ u
              (latitudeFrameAt u) β h J) ≤
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) := by
  obtain ⟨K,C,hK,hC,hgood⟩ :=
    source_mixed_conditioned_latitude_regular μ hQ.1 hnp hM hr0 hr1
  refine ⟨K,C,hK,hC,?_⟩
  intro n hn u hu h k hh hk hband mN
  obtain ⟨hmeas,htail,hreg⟩ := hgood n (by omega) u hu h k hh hk
  dsimp only
  refine ⟨hmeas,htail,?_⟩
  intro J hJ
  exact sourceBand_lower_in_sourceResidual_scale n hn μ hQ u hu J I
    h mN hr0 hr1 hβ hC.le hI hband (hreg J hJ)

/-- The compatible value-only critical-point conditioning has the same
source-scale comparison, including the exact physical residual observable. -/
theorem valueConditioned_sourceBand_residual_comparison
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ h : ℝ, |h| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
      ∀ mN : ℝ,
      let good := sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K
      MeasurableSet good ∧
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu h).real goodᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((n+1:ℕ):ℝ)/2) ∧
      ∀ J ∈ good,
        (2 * Real.exp (-(β*C+2/(1-r^2)^2)/2)) *
          (sourceCriticalBandScale n μ hQ β mN *
            Real.exp (β*(((n+1:ℕ):ℝ)*h-mN)) *
            sourceRadiusCriticalResidualNormalizedPartition n μ hQ u
              (latitudeFrameAt u) β h J) ≤
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) := by
  obtain ⟨K,C,hK,hC,hgood⟩ :=
    source_value_conditioned_latitude_regular μ hQ.1 hM hr0 hr1
  refine ⟨K,C,hK,hC,?_⟩
  intro n hn u hu h hh hband mN
  obtain ⟨hmeas,htail,hreg⟩ := hgood n (by omega) u hu h hh
  dsimp only
  refine ⟨hmeas,htail,?_⟩
  intro J hJ
  exact sourceBand_lower_in_sourceResidual_scale n hn μ hQ u hu J I
    h mN hr0 hr1 hβ hC.le hI hband (hreg J hJ)

/-- The full physical restricted band is a measurable function of every
coefficient tensor, including its correlated quadratic component. -/
theorem sourceBandPartition_measurable
    (n : ℕ) (μ : FiniteMixture) (u : Vector (n+1))
    (I : Set ℝ) (hI : MeasurableSet I) (β : ℝ) :
    Measurable (fun J : Disorder (n+1) μ.maxDegree =>
      partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I)) := by
  have hB : MeasurableSet (overlapRegion u I) :=
    overlapRegion_measurable u hI
  have hBase : StronglyMeasurable
      (fun z : Disorder (n+1) μ.maxDegree × Vector (n+1) =>
        Real.exp (β * field (mixtureCoefficients μ) z.1 z.2)) :=
    (Real.continuous_exp.comp
      (continuous_const.mul
        (field_jointContinuous (mixtureCoefficients μ)))).stronglyMeasurable
  have hJoint : StronglyMeasurable
      (fun z : Disorder (n+1) μ.maxDegree × Vector (n+1) =>
        (overlapRegion u I).indicator
          (fun x => Real.exp (β * field (mixtureCoefficients μ) z.1 x)) z.2) := by
    exact hBase.indicator (hB.preimage measurable_snd)
  have hIntegral := hJoint.integral_prod_right'
    (ν := sphereLaw (n+1)) |>.measurable
  convert hIntegral using 1
  funext J
  dsimp only
  unfold partitionOn
  exact (integral_indicator hB).symm

/-- The normalized literal radius-`√N` residual partition inherits
measurability from the compact-carrier physical integral. -/
theorem sourceRadiusCriticalResidualNormalizedPartition_measurable
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β e₀ : ℝ) :
    Measurable
      (sourceRadiusCriticalResidualNormalizedPartition n μ hQ u e β e₀) := by
  have heq :
      sourceRadiusCriticalResidualNormalizedPartition n μ hQ u e β e₀ =
        actualCriticalResidualNormalizedPartition n μ hQ u e β e₀ := by
    funext J
    exact (actualCriticalResidualNormalizedPartition_eq_sourceRadius
      n hn μ hQ u e β e₀ J).symm
  rw [heq]
  exact actualCriticalResidualNormalizedPartition_measurable n hn μ hQ u e β e₀

end
end SlowEquilibration.SphericalTAPCriticalBandSectionBridge
