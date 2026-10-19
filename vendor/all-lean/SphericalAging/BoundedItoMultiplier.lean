module

public import SphericalAging.VectorItoFormula

public section

/-!
# Bounded past-measurable multipliers of the actual Itô integral

The statement is an identity between the constructed full-filtration
integral operators. The coefficient is measurable at the left end of the
time interval, so multiplying the integrand preserves predictability.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.BoundedItoMultiplier

section GeneralL2
variable {A : Type*} [MeasurableSpace A] {μ : Measure A}
  {C : A → ℝ} (hC : AEStronglyMeasurable C μ) (K : ℝ≥0)
  (hK : ∀ᵐ x ∂μ, ‖C x‖ ≤ K)
include hC K hK

lemma bounded_product_memLp (V : Lp ℝ 2 μ) : MemLp (fun x => C x * V x) 2 μ := by
  apply ((Lp.memLp V).norm.const_mul (K : ℝ)).mono'
    (hC.mul (Lp.aestronglyMeasurable V))
  filter_upwards [hK] with x hx
  change ‖C x * V x‖ ≤ (K : ℝ) * ‖V x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

@[expose] def boundedMul (V : Lp ℝ 2 μ) : Lp ℝ 2 μ := (bounded_product_memLp hC K hK V).toLp _

lemma boundedMul_coe (V : Lp ℝ 2 μ) : (boundedMul hC K hK V : A → ℝ) =ᵐ[μ]
    fun x => C x * V x := MemLp.coeFn_toLp _

lemma boundedMul_norm (V : Lp ℝ 2 μ) : ‖boundedMul hC K hK V‖ ≤ K * ‖V‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMul_coe hC K hK V, hK] with x hx hbound
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

@[expose] def boundedMulCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := boundedMul hC K hK
      map_add' := by
        intro V W
        apply Lp.ext
        filter_upwards [boundedMul_coe hC K hK (V + W), boundedMul_coe hC K hK V,
          boundedMul_coe hC K hK W, Lp.coeFn_add V W,
          Lp.coeFn_add (boundedMul hC K hK V) (boundedMul hC K hK W)]
            with x hVW hV hW hsum hresult
        rw [hVW, hsum, hresult]
        simp only [Pi.add_apply]
        rw [hV, hW]
        ring
      map_smul' := by
        intro c V
        apply Lp.ext
        filter_upwards [boundedMul_coe hC K hK (c • V), boundedMul_coe hC K hK V,
          Lp.coeFn_smul c V, Lp.coeFn_smul c (boundedMul hC K hK V)] with x hc hV hsm hresult
        simp only [RingHom.id_apply]
        change (boundedMul hC K hK (c • V) : A → ℝ) x =
          ((c • boundedMul hC K hK V : Lp ℝ 2 μ) : A → ℝ) x
        rw [hc, hsm, hresult]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hV]
        ring }
    K (boundedMul_norm hC K hK)

lemma boundedMulCLM_coe (V : Lp ℝ 2 μ) : (boundedMulCLM hC K hK V : A → ℝ) =ᵐ[μ]
    fun x => C x * V x := boundedMul_coe hC K hK V
end GeneralL2

open HardSphereDynamics VectorIto
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma intervalCoefficient_bound {a b : ℝ≥0} {C : Ω → ℝ} {K : ℝ≥0}
    (hK : ∀ ω, ‖C ω‖ ≤ K) (p : ℝ≥0 × Ω) :
    ‖elementaryRepresentative 𝓕 a b C p‖ ≤ K := by
  unfold elementaryRepresentative
  split_ifs
  · exact hK _
  · simp

@[expose] def predictableMulCLM {a : ℝ≥0} (b : ℝ≥0) {C : Ω → ℝ}
    (hC : StronglyMeasurable[𝓕 a] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K) :
    PredictableProcessL2 𝓕 P →L[ℝ] PredictableProcessL2 𝓕 P := by
  let G := elementaryRepresentative 𝓕 a b C
  have hG : StronglyMeasurable[𝓕.predictable] G :=
    stronglyMeasurable_elementaryRepresentative 𝓕 a b hC
  let L := boundedMulCLM (μ := nonnegativeLebesgueMeasure.prod P)
    (hG.mono (predictable_le_prod 𝓕)).aestronglyMeasurable K
    (Eventually.of_forall (intervalCoefficient_bound hK))
  let L' := L.comp (PredictableProcessL2 𝓕 P).subtypeL
  refine L'.codRestrict (PredictableProcessL2 𝓕 P) ?_
  intro U
  have heq := boundedMulCLM_coe (hG.mono (predictable_le_prod 𝓕)).aestronglyMeasurable K
    (Eventually.of_forall (intervalCoefficient_bound hK)) (U : TimeProcessL2 P)
  exact (hG.aestronglyMeasurable.mul (lpMeas.aestronglyMeasurable U)).congr heq.symm

omit [IsProbabilityMeasure P] in
lemma predictableMulCLM_coe {a : ℝ≥0} (b : ℝ≥0) {C : Ω → ℝ}
    (hC : StronglyMeasurable[𝓕 a] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (U : PredictableProcessL2 𝓕 P) :
    (predictableMulCLM b hC K hK U : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => elementaryRepresentative 𝓕 a b C p * (U : ℝ≥0 × Ω → ℝ) p :=
  boundedMulCLM_coe
    ((stronglyMeasurable_elementaryRepresentative 𝓕 a b hC).mono
      (predictable_le_prod 𝓕)).aestronglyMeasurable K
    (Eventually.of_forall (intervalCoefficient_bound hK)) (U : TimeProcessL2 P)

@[expose] def adaptedMul {a s : ℝ≥0} {C : Ω → ℝ} (has : a ≤ s)
    (hC : StronglyMeasurable[𝓕 a] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) : lpMeas ℝ ℝ (𝓕 s) 2 P := by
  let V := boundedMulCLM (hC.mono (𝓕.le a)).aestronglyMeasurable K
    (Eventually.of_forall hK) (Z : RandomL2 P)
  refine ⟨V, ?_⟩
  exact ((hC.mono (𝓕.mono has)).aestronglyMeasurable.mul
    (lpMeas.aestronglyMeasurable Z)).congr
      (boundedMulCLM_coe (hC.mono (𝓕.le a)).aestronglyMeasurable K
        (Eventually.of_forall hK) (Z : RandomL2 P)).symm

omit [IsProbabilityMeasure P] in
lemma adaptedMul_coe {a s : ℝ≥0} {C : Ω → ℝ} (has : a ≤ s)
    (hC : StronglyMeasurable[𝓕 a] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) : (adaptedMul has hC K hK Z : Ω → ℝ) =ᵐ[P]
      fun ω => C ω * (Z : Ω → ℝ) ω :=
  boundedMulCLM_coe (hC.mono (𝓕.le a)).aestronglyMeasurable K
    (Eventually.of_forall hK) (Z : RandomL2 P)

lemma predictableMulCLM_elementary {a : ℝ≥0} (b : ℝ≥0) {C : Ω → ℝ}
    (hC : StronglyMeasurable[𝓕 a] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (c d : ℝ≥0) (Z : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    predictableMulCLM b hC K hK (elementaryPredictable 𝓕 c d Z) =
      elementaryPredictable 𝓕 (max c a) (min d b)
        (adaptedMul (le_max_right c a) hC K hK (FourPapersCommon.FilteredBrownian.adaptedMono 𝓕 (le_max_left c a) Z)) := by
  let Y := adaptedMul (le_max_right c a) hC K hK (FourPapersCommon.FilteredBrownian.adaptedMono 𝓕 (le_max_left c a) Z)
  have hY : (Y : Ω → ℝ) =ᵐ[P] fun ω => C ω * (Z : Ω → ℝ) ω :=
    adaptedMul_coe (le_max_right c a) hC K hK _
  have hYprod := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae_eq_comp hY
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableMulCLM_coe b hC K hK (elementaryPredictable 𝓕 c d Z),
    elementaryPredictable_coeFn 𝓕 c d Z,
    elementaryPredictable_coeFn 𝓕 (max c a) (min d b) Y, hYprod] with p h1 h2 h3 hcoef
  rw [h1, h2, h3]
  change (if p.1 ∈ Set.Ioc a b then C p.2 else 0) *
      (if p.1 ∈ Set.Ioc c d then (Z : Ω → ℝ) p.2 else 0) =
      if p.1 ∈ Set.Ioc (max c a) (min d b) then (Y : Ω → ℝ) p.2 else 0
  have hinter : p.1 ∈ Set.Ioc (max c a) (min d b) ↔
      p.1 ∈ Set.Ioc a b ∧ p.1 ∈ Set.Ioc c d := by
    constructor
    · intro h
      exact ⟨⟨lt_of_le_of_lt (le_max_right _ _) h.1, h.2.trans (min_le_right _ _)⟩,
        ⟨lt_of_le_of_lt (le_max_left _ _) h.1, h.2.trans (min_le_left _ _)⟩⟩
    · rintro ⟨ha, hc⟩
      exact ⟨max_lt hc.1 ha.1, le_min hc.2 ha.2⟩
  have hcoef' : (Y : Ω → ℝ) p.2 = C p.2 * (Z : Ω → ℝ) p.2 := hcoef
  by_cases ha : p.1 ∈ Set.Ioc a b <;> by_cases hc : p.1 ∈ Set.Ioc c d <;>
    simp [ha, hc, hinter, hcoef']

lemma coordinateIto_mul_elementary (D : BrownianDriver N P 𝓕) (i : Fin N)
    {a b : ℝ≥0} (hab : a ≤ b) {C : Ω → ℝ} (hC : StronglyMeasurable[𝓕 a] C)
    (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K) (c d : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    coordinateIto D i (predictableMulCLM b hC K hK (elementaryPredictable 𝓕 c d Z)) =
      boundedMulCLM (hC.mono (𝓕.le a)).aestronglyMeasurable K (Eventually.of_forall hK)
        (coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeSlice 𝓕 a b
          (elementaryPredictable 𝓕 c d Z))) := by
  rw [predictableMulCLM_elementary,
    FourPapersCommon.FilteredBrownian.predictableTimeSlice_elementaryPredictable 𝓕 hab c d Z]
  let Z' := FourPapersCommon.FilteredBrownian.adaptedMono 𝓕 (le_max_left c a) Z
  let Y := adaptedMul (le_max_right c a) hC K hK Z'
  by_cases hcd : max c a ≤ min d b
  · unfold coordinateIto
    rw [
      FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hcd,
      FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hcd]
    apply Lp.ext
    filter_upwards [FourPapersCommon.FilteredBrownian.coeFn_elementaryBrownianValue
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hcd Y,
      FourPapersCommon.FilteredBrownian.coeFn_elementaryBrownianValue
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hcd Z',
      adaptedMul_coe (le_max_right c a) hC K hK Z',
      boundedMulCLM_coe (hC.mono (𝓕.le a)).aestronglyMeasurable K
        (Eventually.of_forall hK)
        (FourPapersCommon.FilteredBrownian.elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
          (D.coordinateStronglyMeasurable i) (D.filtered i) hcd Z')] with ω hY hZ hcoef hmul
    rw [hY, hmul, hZ, hcoef]
    ring
  · have hempty : min d b ≤ max c a := le_of_not_ge hcd
    rw [FourPapersCommon.FilteredBrownian.elementaryPredictable_eq_zero_of_le 𝓕 hempty,
      FourPapersCommon.FilteredBrownian.elementaryPredictable_eq_zero_of_le 𝓕 hempty,
      map_zero, map_zero]

/-- A bounded coefficient known at time `a` can be pulled through the
constructed Itô integral over `(a,b]`, even in the enlarged filtration. -/
theorem coordinateIto_mul (D : BrownianDriver N P 𝓕) (i : Fin N)
    {a b : ℝ≥0} (hab : a ≤ b) {C : Ω → ℝ} (hC : StronglyMeasurable[𝓕 a] C)
    (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K) (U : PredictableProcessL2 𝓕 P) :
    coordinateIto D i (predictableMulCLM b hC K hK U) =
      boundedMulCLM (hC.mono (𝓕.le a)).aestronglyMeasurable K (Eventually.of_forall hK)
        (coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeSlice 𝓕 a b U)) := by
  let L := (coordinateIto D i).comp (predictableMulCLM b hC K hK)
  let R := (boundedMulCLM (hC.mono (𝓕.le a)).aestronglyMeasurable K
    (Eventually.of_forall hK)).comp
      ((coordinateIto D i).comp (FourPapersCommon.FilteredBrownian.predictableTimeSliceCLM 𝓕 a b))
  change L U = R U
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable
    (P := P) 𝓕).induction_on U (isClosed_eq L.continuous R.continuous) ?_
  intro v
  have he (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P) :
      L (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x) =
      R (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x) :=
    coordinateIto_mul_elementary D i hab hC K hK x.1 x.2.1.1 x.2.2
  have hv : FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v =
      ∑ x ∈ v.support, v x • FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator 𝓕 P x := by
    simp only [FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable,
      Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hv, map_sum, map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun V => v x • V) (he x))

theorem vectorIto_mul (D : BrownianDriver N P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) {C : Ω → ℝ} (hC : StronglyMeasurable[𝓕 a] C)
    (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K) (U : Fin N → PredictableProcessL2 𝓕 P) :
    vectorIto D (fun i => predictableMulCLM b hC K hK (U i)) =
      boundedMulCLM (hC.mono (𝓕.le a)).aestronglyMeasurable K (Eventually.of_forall hK)
        (vectorIto D (fun i => FourPapersCommon.FilteredBrownian.predictableTimeSlice 𝓕 a b (U i))) := by
  unfold vectorIto
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => coordinateIto_mul D i hab hC K hK (U i))

end SphericalAging.BoundedItoMultiplier
