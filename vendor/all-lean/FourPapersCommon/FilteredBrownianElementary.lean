module

public import StochasticCalculus.ElementaryIto
public import BrownianMotion.Gaussian.BrownianMotion

public section

/-! Brownian elementary integration in a filtration whose complete past is
independent of future increments. This is the filtered extension of the
construction in ElementaryIto, retaining the actual enlarged filtration.
The source proofs are adapted from Ezzeri Esa's MIT-licensed library. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped ENNReal NNReal InnerProductSpace
namespace FourPapersCommon.FilteredBrownian
variable {W : Type*} [MeasurableSpace W]
  {P : Measure W} [IsProbabilityMeasure P] {B : ℝ≥0 → W → ℝ}
omit    
     [IsProbabilityMeasure P]  in
/-- Future Brownian increments are independent of every random variable measurable for a
filtration identified with the natural Brownian filtration. -/
theorem indep_increment_of_natural_adapted
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) {Z : W → ℝ}
    (hZ : AEStronglyMeasurable[𝓕 a] Z P) :
    IndepFun (fun w ↦ B b w - B a w) Z P := by
  let Zm : W → ℝ := hZ.mk Z
  have hZm : @Measurable W ℝ (𝓕 a) inferInstance Zm :=
    hZ.stronglyMeasurable_mk.measurable
  have hindZm := indep_of_indep_of_le_right (hfiltered.indep a b hab) hZm.comap_le
  have hfunZm : IndepFun (fun w ↦ B b w - B a w) Zm P :=
    (IndepFun_iff_Indep _ _ _).mpr hindZm
  exact hfunZm.congr Filter.EventuallyEq.rfl hZ.ae_eq_mk.symm

omit    
     [IsProbabilityMeasure P]  in
/-- An adapted `L²` coefficient times a future Brownian increment is again in `L²`. -/
theorem memLp_natural_adapted_mul_increment
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    MemLp (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) 2 P := by
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := indep_increment_of_natural_adapted hB hsm hfiltered hab
    (lpMeas.aestronglyMeasurable Z)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hint : Integrable ((fun w ↦ (B b w - B a w) ^ 2) *
      fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hindSq.integrable_mul hΔ.integrable_sq
      (Lp.memLp (Z : Lp ℝ 2 P)).integrable_sq
  have hZamb : AEStronglyMeasurable (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.le a) (lpMeas.aestronglyMeasurable Z)
  have hmeas : AEStronglyMeasurable
      (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) P :=
    hZamb.mul hΔ.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine hint.congr (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply]
  ring

/-- The genuine Brownian terminal value `Z (B_b - B_a)` of an adapted elementary process. -/
@[expose] noncomputable def elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : RandomL2 P :=
  (memLp_natural_adapted_mul_increment hB hsm hfiltered hab Z).toLp
    (fun w ↦ (Z : W → ℝ) w * (B b w - B a w))

omit    
     [IsProbabilityMeasure P]  in
/-- A representative of the constructed elementary Brownian terminal value. -/
theorem coeFn_elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryBrownianValue hB hsm hfiltered hab Z : W → ℝ) =ᵐ[P]
      fun w ↦ (Z : W → ℝ) w * (B b w - B a w) :=
  MemLp.coeFn_toLp _

omit    
     [IsProbabilityMeasure P]  in
/-- The elementary Brownian terminal value is additive in its adapted coefficient. -/
theorem elementaryBrownianValue_add
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hfiltered hab (Z + Y) =
      elementaryBrownianValue hB hsm hfiltered hab Z +
        elementaryBrownianValue hB hsm hfiltered hab Y := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hfiltered hab (Z + Y),
    coeFn_elementaryBrownianValue hB hsm hfiltered hab Z,
    coeFn_elementaryBrownianValue hB hsm hfiltered hab Y,
    Lp.coeFn_add (Z : RandomL2 P) (Y : RandomL2 P),
    Lp.coeFn_add (elementaryBrownianValue hB hsm hfiltered hab Z)
      (elementaryBrownianValue hB hsm hfiltered hab Y)]
    with w hsum hZ hY hZY hvalue
  rw [hsum, hvalue, Pi.add_apply, hZ, hY]
  change (Z.1 + Y.1 : RandomL2 P) w * (B b w - B a w) =
    (Z : W → ℝ) w * (B b w - B a w) +
      (Y : W → ℝ) w * (B b w - B a w)
  rw [hZY, Pi.add_apply]
  ring

omit    
     [IsProbabilityMeasure P]  in
/-- The elementary Brownian terminal value commutes with real scalar multiplication. -/
theorem elementaryBrownianValue_smul
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (c : ℝ) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hfiltered hab (c • Z) =
      c • elementaryBrownianValue hB hsm hfiltered hab Z := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hfiltered hab (c • Z),
    coeFn_elementaryBrownianValue hB hsm hfiltered hab Z,
    Lp.coeFn_smul c (Z : RandomL2 P),
    Lp.coeFn_smul c (elementaryBrownianValue hB hsm hfiltered hab Z)]
    with w hsmul hZ hcZ hvalue
  rw [hsmul, hvalue, Pi.smul_apply, hZ]
  change (c • Z.1 : RandomL2 P) w * (B b w - B a w) =
    c • ((Z : W → ℝ) w * (B b w - B a w))
  rw [hcZ, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- For a fixed interval, the genuine Brownian terminal value is a linear function of the
adapted coefficient. -/
@[expose] noncomputable def elementaryBrownianValueLinear
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) : lpMeas ℝ ℝ (𝓕 a) 2 P →ₗ[ℝ] RandomL2 P where
  toFun := elementaryBrownianValue hB hsm hfiltered hab
  map_add' := elementaryBrownianValue_add hB hsm hfiltered hab
  map_smul' := elementaryBrownianValue_smul hB hsm hfiltered hab

omit    
     [IsProbabilityMeasure P]  in
/-- The fixed-interval linear map evaluates to the elementary Brownian value. -/
@[simp]
theorem elementaryBrownianValueLinear_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValueLinear hB hsm hfiltered hab Z =
      elementaryBrownianValue hB hsm hfiltered hab Z :=
  rfl

omit    
     [IsProbabilityMeasure P]  in
/-- Constructed elementary Brownian values on chronologically disjoint intervals are
orthogonal. -/
theorem inner_elementaryBrownianValue_eq_zero_of_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hfiltered hab Z)
      (elementaryBrownianValue hB hsm hfiltered hcd Y) = 0 := by
  have hac : a ≤ c := hab.trans hbc
  have hBadapted : StronglyAdapted 𝓕 B := hfiltered.stronglyAdapted
  have hZc : AEStronglyMeasurable[𝓕 c] (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.mono hac) (lpMeas.aestronglyMeasurable Z)
  have hYc : AEStronglyMeasurable[𝓕 c] (Y : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Y
  have hΔabc : AEStronglyMeasurable[𝓕 c] (fun w ↦ B b w - B a w) P :=
    ((hBadapted.stronglyMeasurable_le hbc).sub
      (hBadapted.stronglyMeasurable_le hac)).aestronglyMeasurable
  have hG : AEStronglyMeasurable[𝓕 c]
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    (hZc.mul hΔabc).mul hYc
  have hind := indep_increment_of_natural_adapted hB hsm hfiltered hcd hG
  have hΔcd : AEStronglyMeasurable (fun w ↦ B d w - B c w) P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  have hGamb : AEStronglyMeasurable
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    AEStronglyMeasurable.mono (𝓕.le c) hG
  have hfactor := hind.integral_mul_eq_mul_integral hΔcd hGamb
  rw [L2.inner_def]
  calc
    ∫ w, ⟪elementaryBrownianValue hB hsm hfiltered hab Z w,
        elementaryBrownianValue hB hsm hfiltered hcd Y w⟫_ℝ ∂P =
        ∫ w, (B d w - B c w) *
          (((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_elementaryBrownianValue hB hsm hfiltered hab Z,
        coeFn_elementaryBrownianValue hB hsm hfiltered hcd Y] with w hfirst hsecond
      rw [hfirst, hsecond]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ w, B d w - B c w ∂P) *
        ∫ w, ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (hB.integrable_eval d) (hB.integrable_eval c),
        hB.integral_eval, hB.integral_eval, sub_zero, zero_mul]

omit    
     [IsProbabilityMeasure P]  in
/-- The cross-inner-product identity for chronologically disjoint constructed elementary
Brownian values. -/
theorem inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le [SFinite P]
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hfiltered hab Z)
      (elementaryBrownianValue hB hsm hfiltered hcd Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 c d Y) := by
  rw [inner_elementaryBrownianValue_eq_zero_of_le hB hsm hfiltered hab hbc hcd Z Y,
    inner_elementaryPredictable_eq_zero_of_le 𝓕 hbc Z Y]

/-- The cross-inner-product identity for two constructed elementary Brownian values on the same
interval. -/
theorem inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hfiltered hab Z)
      (elementaryBrownianValue hB hsm hfiltered hab Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 a b Y) := by
  have hZY : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (indep_increment_of_natural_adapted hB hsm hfiltered hab hZY).comp
      (measurable_id.pow_const 2) measurable_id
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hfactor := hindSq.integral_mul_eq_mul_integral
    hΔ.integrable_sq.aestronglyMeasurable
    (AEStronglyMeasurable.mono (𝓕.le a) hZY)
  have hout : inner ℝ (elementaryBrownianValue hB hsm hfiltered hab Z)
      (elementaryBrownianValue hB hsm hfiltered hab Y) =
        (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
    rw [L2.inner_def]
    calc
      ∫ w, ⟪elementaryBrownianValue hB hsm hfiltered hab Z w,
          elementaryBrownianValue hB hsm hfiltered hab Y w⟫_ℝ ∂P =
          ∫ w, (B b w - B a w) ^ 2 *
            ((Z : W → ℝ) w * (Y : W → ℝ) w) ∂P := by
        apply integral_congr_ae
        filter_upwards [coeFn_elementaryBrownianValue hB hsm hfiltered hab Z,
          coeFn_elementaryBrownianValue hB hsm hfiltered hab Y] with w hfirst hsecond
        rw [hfirst, hsecond]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      _ = (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
        simpa only [Pi.mul_apply] using hfactor
  have hinc : inner ℝ (brownianLp hB b - brownianLp hB a)
      (brownianLp hB b - brownianLp hB a) =
        inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← wienerIntegral_indicatorConstLp_Ioc hB hab, inner_wienerIntegral]
    rfl
  have hΔtime : (∫ w, (B b w - B a w) ^ 2 ∂P) =
      inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← hinc, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
      coeFn_brownianLp hB b, coeFn_brownianLp hB a] with w hsub hb ha
    rw [hsub]
    simp only [Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    rw [hb, ha]
    ring
  have hZYinner : (∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P) =
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards with w
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [hout, hΔtime, hZYinner]
  change inner ℝ (iocIndicator a b) (iocIndicator a b) *
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) =
    inner ℝ (tensor (iocIndicator a b) (Z : RandomL2 P))
      (tensor (iocIndicator a b) (Y : RandomL2 P))
  rw [inner_tensor]


end FourPapersCommon.FilteredBrownian
