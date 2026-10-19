module

public import SphericalAging.HardSphereDynamics
public import FourPapersCommon.FilteredItoContinuous
public import SphericalAging.AdaptedContinuous
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic

public section

/-!
# Full-filtration finite-dimensional stochastic integration

The driving data include joint increment independence from the complete
filtration. VectorBrownian constructs these data on the actual product
continuous-path law, also with independent initial point and disorder.
The cross-coordinate identities below are proved for the constructed
Brownian integrals; they are not radial Itô identities supplied as hypotheses.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace

namespace SphericalAging.VectorIto

open HardSphereDynamics

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def increment (D : BrownianDriver N P 𝓕) (i : Fin N) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  D.coordinate i t ω - D.coordinate i s ω

omit [IsProbabilityMeasure P] in
lemma increment_measurable (D : BrownianDriver N P 𝓕) (i : Fin N) (s t : ℝ≥0) :
    Measurable (increment D i s t) :=
  (D.coordinateStronglyMeasurable i t).measurable.sub
    (D.coordinateStronglyMeasurable i s).measurable

omit [IsProbabilityMeasure P] in
lemma increment_memLp_two (D : BrownianDriver N P 𝓕) (i : Fin N) (s t : ℝ≥0) :
    MemLp (increment D i s t) 2 P :=
  (D.filtered i).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_sub.memLp_two

omit [IsProbabilityMeasure P] in
lemma increment_integral (D : BrownianDriver N P 𝓕) (i : Fin N) (s t : ℝ≥0) :
    ∫ ω, increment D i s t ω ∂P = 0 := by
  unfold increment
  rw [integral_sub ((D.filtered i).integrable_eval t) ((D.filtered i).integrable_eval s),
    (D.filtered i).integral_eval, (D.filtered i).integral_eval, sub_self]

omit [IsProbabilityMeasure P] in
lemma increments_independent (D : BrownianDriver N P 𝓕) (s t : ℝ≥0) :
    iIndepFun (fun i => increment D i s t) P := by
  exact D.independent.comp (fun _ (f : ℝ≥0 → ℝ) => f t - f s)
    (fun _ => (measurable_pi_apply t).sub (measurable_pi_apply s))

lemma gaussian_zero_second_moment (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  change Var[(id : ℝ → ℝ); gaussianReal 0 v] = (v : ℝ) at h
  rw [variance_of_integral_eq_zero aemeasurable_id (by simp)] at h
  exact h

omit [IsProbabilityMeasure P] in
omit [IsProbabilityMeasure P] in
lemma increment_integral_sq (D : BrownianDriver N P 𝓕) (i : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, increment D i s t ω ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
  have hl := (D.filtered i).hasLaw_sub t s
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) :=
      hl.integral_comp (measurable_id.pow_const 2).aestronglyMeasurable
    _ = (nndist (t : ℝ) (s : ℝ) : ℝ) := gaussian_zero_second_moment _
    _ = (t : ℝ) - (s : ℝ) := by
      rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hst))]

omit [IsProbabilityMeasure P] in
lemma increment_cross_integral (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (s t : ℝ≥0) :
    ∫ ω, increment D i s t ω * increment D j s t ω ∂P = 0 := by
  rw [((increments_independent D s t).indepFun hij).integral_fun_mul_eq_mul_integral
    (increment_memLp_two D i s t).aestronglyMeasurable
    (increment_memLp_two D j s t).aestronglyMeasurable,
    increment_integral D i s t, zero_mul]

omit [IsProbabilityMeasure P] in
lemma increment_product_indep_adapted (D : BrownianDriver N P 𝓕) (i j : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : AEStronglyMeasurable[𝓕 s] Z P) :
    IndepFun (fun ω => increment D i s t ω * increment D j s t ω) Z P := by
  let Zm := hZ.mk Z
  have hZm : Measurable[𝓕 s] Zm := hZ.stronglyMeasurable_mk.measurable
  have hvec : IndepFun (fun ω k => increment D k s t ω) Zm P :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (D.jointFiltered s t hst) hZm.comap_le)
  have hp : Measurable (fun f : Fin N → ℝ => f i * f j) :=
    (measurable_pi_apply i).mul (measurable_pi_apply j)
  exact (hvec.comp hp measurable_id).congr EventuallyEq.rfl hZ.ae_eq_mk.symm

omit [IsProbabilityMeasure P] in
/-- Same-interval weighted cross-coordinate covariance is exactly zero,
even though both adapted weights may depend on every Brownian coordinate. -/
lemma weighted_cross_increment_integral (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) {s t : ℝ≥0} (hst : s ≤ t)
    (Z Y : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    ∫ ω, ((Z : Ω → ℝ) ω * increment D i s t ω) *
      ((Y : Ω → ℝ) ω * increment D j s t ω) ∂P = 0 := by
  have hC : AEStronglyMeasurable[𝓕 s]
      (fun ω => (Z : Ω → ℝ) ω * (Y : Ω → ℝ) ω) P :=
    (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hi := increment_product_indep_adapted D i j hst hC
  calc
    _ = ∫ ω, (increment D i s t ω * increment D j s t ω) *
        ((Z : Ω → ℝ) ω * (Y : Ω → ℝ) ω) ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => by ring)
    _ = (∫ ω, increment D i s t ω * increment D j s t ω ∂P) *
        ∫ ω, (Z : Ω → ℝ) ω * (Y : Ω → ℝ) ω ∂P := by
      exact hi.integral_fun_mul_eq_mul_integral
        ((increment_memLp_two D i s t).aestronglyMeasurable.mul
          (increment_memLp_two D j s t).aestronglyMeasurable)
        (hC.mono (𝓕.le s))
    _ = 0 := by rw [increment_cross_integral D hij s t, zero_mul]

omit [IsProbabilityMeasure P] in
/-- The mixed product is genuinely integrable, so the covariance identity
above does not rely on the undefined-integral convention. -/
lemma weighted_cross_increment_integrable (D : BrownianDriver N P 𝓕) (i j : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) (Z Y : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    Integrable (fun ω => ((Z : Ω → ℝ) ω * increment D i s t ω) *
      ((Y : Ω → ℝ) ω * increment D j s t ω)) P := by
  have hC := (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hi := increment_product_indep_adapted D i j hst hC
  have hΔ := (increment_memLp_two D i s t).integrable_mul (increment_memLp_two D j s t)
  have hZY := (Lp.memLp (Z : Lp ℝ 2 P)).integrable_mul (Lp.memLp (Y : Lp ℝ 2 P))
  exact (hi.integrable_mul hΔ hZY).congr (Eventually.of_forall (fun _ => by
    simp only [Pi.mul_apply]
    ring))

@[expose] def elementaryValue (D : BrownianDriver N P 𝓕) (i : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) : RandomL2 P :=
  FourPapersCommon.FilteredBrownian.elementaryBrownianValue
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z

omit [IsProbabilityMeasure P] in
lemma elementaryValue_coe (D : BrownianDriver N P 𝓕) (i : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    (elementaryValue D i hst Z : Ω → ℝ) =ᵐ[P]
      fun ω => (Z : Ω → ℝ) ω * increment D i s t ω :=
  FourPapersCommon.FilteredBrownian.coeFn_elementaryBrownianValue
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z

omit [IsProbabilityMeasure P] in
lemma inner_elementaryValue_cross_same (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) {s t : ℝ≥0} (hst : s ≤ t) (Z Y : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    inner ℝ (elementaryValue D i hst Z) (elementaryValue D j hst Y) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ ω, ((Z : Ω → ℝ) ω * increment D i s t ω) *
        ((Y : Ω → ℝ) ω * increment D j s t ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [elementaryValue_coe D i hst Z, elementaryValue_coe D j hst Y]
        with ω hZ hY
      rw [hZ, hY]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = 0 := weighted_cross_increment_integral D hij hst Z Y

lemma inner_elementaryValue_same (D : BrownianDriver N P 𝓕) (i : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) (Z Y : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    inner ℝ (elementaryValue D i hst Z) (elementaryValue D i hst Y) =
      inner ℝ (elementaryPredictable 𝓕 s t Z) (elementaryPredictable 𝓕 s t Y) :=
  FourPapersCommon.FilteredBrownian.inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z Y

omit [IsProbabilityMeasure P] in
lemma inner_elementaryValue_disjoint (D : BrownianDriver N P 𝓕) (i j : Fin N)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryValue D i hab Z) (elementaryValue D j hcd Y) = 0 := by
  have hac : a ≤ c := hab.trans hbc
  have hBadapted := (D.filtered i).stronglyAdapted
  have hZc := (lpMeas.aestronglyMeasurable Z).mono (𝓕.mono hac)
  have hYc := lpMeas.aestronglyMeasurable Y
  have hΔc : AEStronglyMeasurable[𝓕 c] (increment D i a b) P :=
    ((hBadapted.stronglyMeasurable_le hbc).sub
      (hBadapted.stronglyMeasurable_le hac)).aestronglyMeasurable
  have hG : AEStronglyMeasurable[𝓕 c]
      (fun ω => ((Z : Ω → ℝ) ω * increment D i a b ω) * (Y : Ω → ℝ) ω) P :=
    (hZc.mul hΔc).mul hYc
  have hi := FourPapersCommon.FilteredBrownian.indep_increment_of_natural_adapted
    (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) hcd hG
  have hfactor := hi.integral_fun_mul_eq_mul_integral
    (increment_memLp_two D j c d).aestronglyMeasurable (hG.mono (𝓕.le c))
  rw [L2.inner_def]
  calc
    _ = ∫ ω, increment D j c d ω *
        (((Z : Ω → ℝ) ω * increment D i a b ω) * (Y : Ω → ℝ) ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [elementaryValue_coe D i hab Z, elementaryValue_coe D j hcd Y]
        with ω hZ hY
      rw [hZ, hY]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ ω, increment D j c d ω ∂P) *
        (∫ ω, ((Z : Ω → ℝ) ω * increment D i a b ω) * (Y : Ω → ℝ) ω ∂P) := hfactor
    _ = 0 := by rw [increment_integral D j c d, zero_mul]

omit [IsProbabilityMeasure P] in
lemma elementaryValue_split (D : BrownianDriver N P 𝓕) (i : Fin N)
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryValue D i (hac.trans hcb) Z = elementaryValue D i hac Z +
      elementaryValue D i hcb (adaptedMono 𝓕 hac Z) := by
  apply Lp.ext
  filter_upwards [elementaryValue_coe D i (hac.trans hcb) Z,
    elementaryValue_coe D i hac Z, elementaryValue_coe D i hcb (adaptedMono 𝓕 hac Z),
    Lp.coeFn_add (elementaryValue D i hac Z)
      (elementaryValue D i hcb (adaptedMono 𝓕 hac Z))] with ω habω hacω hcbω hadd
  rw [habω, hadd, Pi.add_apply, hacω, hcbω]
  change (Z : Ω → ℝ) ω * (D.coordinate i b ω - D.coordinate i a ω) =
    (Z : Ω → ℝ) ω * (D.coordinate i c ω - D.coordinate i a ω) +
      (Z : Ω → ℝ) ω * (D.coordinate i b ω - D.coordinate i c ω)
  ring

omit [IsProbabilityMeasure P] in
/-- Elementary stochastic integrals against different driving coordinates
are orthogonal for arbitrary overlapping time intervals. -/
lemma inner_elementaryValue_cross (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryValue D i hab Z) (elementaryValue D j hcd Y) = 0 := by
  have hordered : ∀ {i j : Fin N}, i ≠ j → ∀ {a b c d : ℝ≥0}
      (hab : a ≤ b) (hcd : c ≤ d) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P)
      (Y : lpMeas ℝ ℝ (𝓕 c) 2 P), a ≤ c →
      inner ℝ (elementaryValue D i hab Z) (elementaryValue D j hcd Y) = 0 := by
    intro i j hij a b c d hab hcd Z Y hac
    by_cases hbc : b ≤ c
    · exact inner_elementaryValue_disjoint D i j hab hbc hcd Z Y
    have hcb : c ≤ b := le_of_lt (lt_of_not_ge hbc)
    let Zc := adaptedMono 𝓕 hac Z
    rw [elementaryValue_split D i hac hcb Z]
    by_cases hbd : b ≤ d
    · let Yb := adaptedMono 𝓕 hcb Y
      rw [elementaryValue_split D j hcb hbd Y]
      simp only [inner_add_left, inner_add_right]
      rw [inner_elementaryValue_disjoint D i j hac le_rfl hcb Z Y,
        inner_elementaryValue_disjoint D i j hac hcb hbd Z Yb,
        inner_elementaryValue_cross_same D hij hcb Zc Y,
        inner_elementaryValue_disjoint D i j hcb le_rfl hbd Zc Yb]
      simp
    · have hdb : d ≤ b := le_of_lt (lt_of_not_ge hbd)
      let Zd := adaptedMono 𝓕 hcd Zc
      have hrev : inner ℝ (elementaryValue D i hdb Zd) (elementaryValue D j hcd Y) = 0 := by
        rw [real_inner_comm]
        exact inner_elementaryValue_disjoint D j i hcd le_rfl hdb Y Zd
      rw [elementaryValue_split D i hcd hdb Zc]
      simp only [inner_add_left]
      rw [inner_elementaryValue_disjoint D i j hac le_rfl hcd Z Y,
        inner_elementaryValue_cross_same D hij hcd Zc Y, hrev]
      simp
  rcases le_total a c with hac | hca
  · exact hordered hij hab hcd Z Y hac
  · rw [real_inner_comm]
    exact hordered hij.symm hcd hab Y Z hca

@[expose] def coordinateIto (D : BrownianDriver N P 𝓕) (i : Fin N) :
    PredictableProcessL2 𝓕 P →L[ℝ] RandomL2 P :=
  FourPapersCommon.FilteredBrownian.naturalItoIntegral
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i)

omit [IsProbabilityMeasure P] in
lemma inner_elementary_combinations_cross (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j)
    (v w : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    inner ℝ (FourPapersCommon.FilteredBrownian.elementaryFinsuppToBrownian
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) v)
      (FourPapersCommon.FilteredBrownian.elementaryFinsuppToBrownian
        (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) w) = 0 := by
  unfold FourPapersCommon.FilteredBrownian.elementaryFinsuppToBrownian
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  have h := inner_elementaryValue_cross D hij y.2.1.2 x.2.1.2 y.2.2 x.2.2
  change inner ℝ (FourPapersCommon.FilteredBrownian.elementaryBrownianGenerator
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) y)
    (FourPapersCommon.FilteredBrownian.elementaryBrownianGenerator
      (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) x) = 0 at h
  simp only [h, mul_zero]

/-- Full-filtration Itô integrals against distinct coordinates are orthogonal
for every predictable L2 integrand, by the actual elementary-density closure. -/
lemma inner_coordinateIto_cross (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (U V : PredictableProcessL2 𝓕 P) :
    inner ℝ (coordinateIto D i U) (coordinateIto D j V) = 0 := by
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable
    (P := P) 𝓕).induction_on₂ (p := fun U V =>
      inner ℝ (coordinateIto D i U) (coordinateIto D j V) = 0) ?_ ?_ U V
  · exact isClosed_eq (((coordinateIto D i).continuous.comp continuous_fst).inner
      ((coordinateIto D j).continuous.comp continuous_snd)) continuous_const
  · intro v w
    unfold coordinateIto
    rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryFinsuppToPredictable,
      FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryFinsuppToPredictable]
    exact inner_elementary_combinations_cross D hij v w

lemma inner_coordinateIto_same (D : BrownianDriver N P 𝓕) (i : Fin N)
    (U V : PredictableProcessL2 𝓕 P) :
    inner ℝ (coordinateIto D i U) (coordinateIto D i V) = inner ℝ U V :=
  FourPapersCommon.FilteredBrownian.inner_naturalItoIntegral
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U V

@[expose] def vectorIto (D : BrownianDriver N P 𝓕) (U : Fin N → PredictableProcessL2 𝓕 P) : RandomL2 P :=
  ∑ i, coordinateIto D i (U i)

/-- Genuine multivariate Itô isometry with the entire driving filtration. -/
lemma inner_vectorIto (D : BrownianDriver N P 𝓕)
    (U V : Fin N → PredictableProcessL2 𝓕 P) :
    inner ℝ (vectorIto D U) (vectorIto D V) = ∑ i, inner ℝ (U i) (V i) := by
  unfold vectorIto
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact inner_coordinateIto_same D i (U i) (V i)
  · intro j _ hji
    exact inner_coordinateIto_cross D hji (U j) (V i)
  · simp

lemma norm_sq_vectorIto (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) :
    ‖vectorIto D U‖ ^ 2 = ∑ i, ‖U i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vectorIto]
  simp only [real_inner_self_eq_norm_sq]

/-- The finite-dimensional stochastic integral is an actual continuous linear map. -/
@[expose] def vectorItoCLM (D : BrownianDriver N P 𝓕) :
    (Fin N → PredictableProcessL2 𝓕 P) →L[ℝ] RandomL2 P :=
  ∑ i, (coordinateIto D i).comp (ContinuousLinearMap.proj i)

omit [IsProbabilityMeasure P] in
lemma vectorItoCLM_apply (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) : vectorItoCLM D U = vectorIto D U := by
  simp [vectorItoCLM, vectorIto]

@[expose] def coordinateProcess (D : BrownianDriver N P 𝓕) (i : Fin N)
    (U : PredictableProcessL2 𝓕 P) : ℝ≥0 → Ω → ℝ :=
  FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U

@[expose] def vectorProcess (D : BrownianDriver N P 𝓕) (U : Fin N → PredictableProcessL2 𝓕 P) :
    ℝ≥0 → Ω → ℝ := fun t ω => ∑ i, coordinateProcess D i (U i) t ω

@[expose] def vectorProcessLp (D : BrownianDriver N P 𝓕) (U : Fin N → PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) : RandomL2 P :=
  vectorIto D (fun i => FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t (U i))

lemma vectorProcessLp_ae_eq (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    (vectorProcessLp D U t : Ω → ℝ) =ᵐ[P] vectorProcess D U t := by
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin N,
      (coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t (U i)) :
        Ω → ℝ) ω = coordinateProcess D i (U i) t ω :=
    ae_all_iff.mpr (fun i => FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) (U i) t)
  filter_upwards [hall, Lp.coeFn_finsetSum Finset.univ (fun i =>
    coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t (U i)))]
      with ω hω hsum
  simp only [Finset.sum_apply] at hsum
  exact hsum.trans (Finset.sum_congr rfl (fun i _ => hω i))

lemma vectorProcess_memLp_two (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t : ℝ≥0) : MemLp (vectorProcess D U t) 2 P :=
  MemLp.ae_eq (vectorProcessLp_ae_eq D U t) (Lp.memLp (vectorProcessLp D U t))

lemma martingale_vectorProcess (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) : Martingale (vectorProcess D U) 𝓕 P := by
  have hM (i : Fin N) : Martingale (coordinateProcess D i (U i)) 𝓕 P :=
    FourPapersCommon.FilteredBrownian.martingale_naturalItoProcessRepresentative
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) (U i)
  have hsum (S : Finset (Fin N)) : Martingale
      (fun t ω => ∑ i ∈ S, coordinateProcess D i (U i) t ω) 𝓕 P := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact martingale_zero ℝ 𝓕 P
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hM i).add ih
  exact hsum Finset.univ

/-- Finite-dimensional constructed Itô integrals have actual continuous
modifications in the complete driving filtration's probability space. -/
lemma exists_continuousModification_vectorProcess (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsContinuousProcessModification (vectorProcess D U) Y P := by
  have hi (i : Fin N) :=
    FourPapersCommon.FilteredBrownian.exists_continuousModification_naturalItoProcess
      (D.brownian i) (D.coordinateStronglyMeasurable i) (D.filtered i) (U i)
  choose Y hY using hi
  refine ⟨fun t ω => ∑ i, Y i t ω, ?_⟩
  constructor
  · intro t
    have hall : ∀ᵐ ω ∂P, ∀ i : Fin N, coordinateProcess D i (U i) t ω = Y i t ω :=
      ae_all_iff.mpr (fun i => (hY i).fixedTime_ae_eq t)
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl (fun i _ => hω i)
  · have hall : ∀ᵐ ω ∂P, ∀ i : Fin N, Continuous (fun t => Y i t ω) :=
      ae_all_iff.mpr (fun i => (hY i).continuous_paths)
    filter_upwards [hall] with ω hω
    exact continuous_finsetSum Finset.univ (fun i _ => hω i)

lemma vectorProcessLp_norm_sq (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ‖vectorProcessLp D U t‖ ^ 2 =
      ∑ i, ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t (U i)‖ ^ 2 :=
  norm_sq_vectorIto D _

lemma integral_sq_vectorProcess (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ∫ ω, vectorProcess D U t ω ^ 2 ∂P =
      ∑ i, ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t (U i)‖ ^ 2 := by
  calc
    _ = ∫ ω, (vectorProcessLp D U t : Ω → ℝ) ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [vectorProcessLp_ae_eq D U t] with ω hω
      rw [hω]
    _ = inner ℝ (vectorProcessLp D U t) (vectorProcessLp D U t) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => by simp [pow_two])
    _ = ‖vectorProcessLp D U t‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = _ := vectorProcessLp_norm_sq D U t

/-- The vector stochastic integral has a continuous martingale version in
the original filtration, including the background information at time zero. -/
lemma exists_continuous_martingale_vectorProcess (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓕 P ∧
      IsContinuousProcessModification (vectorProcess D U) Y P := by
  obtain ⟨Y, hY⟩ := exists_continuousModification_vectorProcess D U
  exact AdaptedContinuous.exists_continuous_martingale_modification
    (martingale_vectorProcess D U) hY

end SphericalAging.VectorIto
