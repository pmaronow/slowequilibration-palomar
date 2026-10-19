-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedFilterInterface
public import SlowEquilibration.SourceMixedOnePointLiteral
public import SlowEquilibration.SourcePureDeterminantDerivative
public import SlowEquilibration.SphericalMarkedRadialTheorem
public import SlowEquilibration.SphericalTAPMixedSaddleClearanceChoice
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Topology.Algebra.MvPolynomial

/-! Completion of the one-point interfaces in manuscript Section 10.
The Palm laws below are measurable kernels on the original disorder, with
actual negative-Hessian determinant weights. Raw energy is used throughout.
Admissibility refers to all four printed conditions, including the global
radial saddle and the distance to the complement of the chosen interval.
The exported packages do not assert simultaneous retention of every high
critical point, or a single mixed/pure localization-and-filter corollary.
The pure scalar normalization package records density, count and tail limits;
it does not assert all finite-dimension microscopic envelopes. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMixedOnePointComplete
open MeasureTheory ProbabilityTheory Set Filter Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalMarkedWindows SphericalSequentialRegression SphericalPosteriorMaps
open WholeFieldRegression IntrinsicHessianLaw
open SphericalTAPCertificate TwoAtomStationarity LatitudeGroundTrial
open PairConditionalDeterminantMoments ConditionedDeterminantMoments GOEMaximumDeterminant
open SourceMixedOnePointLiteral SourceMixedFilterInterface SourcePureDeterminantDerivative
open GOEAsymptotics GOEClippedDeterminants GOERawMoments Polynomial
open scoped ENNReal NNReal Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def mixedPosteriorKernel (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    Kernel (ℝ × ℝ) (Disorder (n+2) μ.maxDegree) :=
  (WholeFieldRegression.coefficientKernel
    (WholeFieldRegression.jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u (tangentFrame u hu))).comap
      (fun z => jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • scorePairEquiv z))
      ((jointScoreTarget_continuous (n+1)).measurable.comp (by fun_prop))

instance mixedPosteriorKernel_markov (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    IsMarkovKernel (mixedPosteriorKernel n μ Q u hu) := by
  unfold mixedPosteriorKernel
  infer_instance

def negativeDetWeight (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (J : Disorder (n+2) μ.maxDegree) : ℝ≥0∞ :=
  ENNReal.ofReal |(intrinsicHessian
    (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det| *
      negativeHessianMark (n+1) (centerCoefficients (mixtureCoefficients μ) Q) J u

private lemma negativeDetWeight_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    Measurable (negativeDetWeight n μ Q u) :=
  (intrinsicDet_measurable _ u hu).mul
    ((negativeHessianMark_measurable (n+1) _).comp (measurable_id.prodMk measurable_const))

def mixedPalmWeight (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (z : ℝ × ℝ) (w : Disorder (n+2) μ.maxDegree × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(n+2:ℕ)/2 * scoreQuadratic μ Q (scorePairEquiv z))) *
    negativeDetWeight n μ Q u w.1

private lemma mixedPalmWeight_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    Measurable (uncurry (mixedPalmWeight n μ Q u)) := by
  have hq : Measurable (fun z : ℝ × ℝ => scoreQuadratic μ Q (scorePairEquiv z)) := by
    change Measurable (fun z : ℝ × ℝ => scoreQuadratic μ Q (scorePairEquiv (z.1,z.2)))
    simp_rw [source_scoreQuadratic_precision_form]
    fun_prop
  exact (measurable_const.mul (hq.comp measurable_fst)).exp.ennreal_ofReal.mul
    ((negativeDetWeight_measurable n μ Q u hu).comp measurable_snd.fst)

def mixedPalmNumerator (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (U : Set ℝ) :
    Kernel ℝ (Disorder (n+2) μ.maxDegree × ℝ) :=
  ((mixedPosteriorKernel n μ Q u hu ×ₖ Kernel.deterministic Prod.snd measurable_snd).withDensity
    (mixedPalmWeight n μ Q u)) ∘ₖ (Kernel.id ×ₖ Kernel.const ℝ (volume.restrict U))

private lemma mixedPalmNumerator_formula (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (U : Set ℝ) (e : ℝ)
    (f : Disorder (n+2) μ.maxDegree × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f w ∂mixedPalmNumerator n μ Q u hu U e) =
      ∫⁻ k in U, ENNReal.ofReal (Real.exp (-(n+2:ℕ)/2*
        scoreQuadratic μ Q (scorePairEquiv (e,k)))) *
          ∫⁻ J, negativeDetWeight n μ Q u J * f (J,k)
            ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
              (scorePairEquiv (e,k)) := by
  rw [mixedPalmNumerator, Kernel.lintegral_comp _ _ _ hf,
    Kernel.lintegral_id_prod hf.lintegral_kernel _ e]
  apply lintegral_congr
  intro k
  rw [Kernel.lintegral_withDensity _ (mixedPalmWeight_measurable n μ Q u hu) _ hf,
    Kernel.lintegral_prod_deterministic measurable_snd _ _
      (g := fun b => mixedPalmWeight n μ Q u (e,k) b * f b)
      (((mixedPalmWeight_measurable n μ Q u hu).comp
        (measurable_const.prodMk measurable_id)).mul hf)]
  change (∫⁻ J, (ENNReal.ofReal _ * negativeDetWeight n μ Q u J) * f (J,k)
    ∂mixedConditionedLaw _ u hu (scorePairEquiv (e,k))) = _
  simp_rw [mul_assoc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

instance mixedPalmNumerator_sfinite (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (U : Set ℝ) :
    IsSFiniteKernel (mixedPalmNumerator n μ Q u hu U) := by
  have : IsSFiniteKernel
      ((mixedPosteriorKernel n μ Q u hu ×ₖ Kernel.deterministic Prod.snd measurable_snd).withDensity
        (mixedPalmWeight n μ Q u)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro z w
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    unfold negativeHessianMark
    split_ifs <;> simp
  unfold mixedPalmNumerator
  infer_instance

/-- The actual mixed energy-Palm kernel, measurable in normalized energy.
Its denominator is its raw determinant mass, never the physical intensity. -/
def mixedMaximumPalmKernel (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (U : Set ℝ) :
    Kernel ℝ (Disorder (n+2) μ.maxDegree × ℝ) :=
  (mixedPalmNumerator n μ Q u hu U).withDensity
    (fun e _ => (mixedPalmNumerator n μ Q u hu U e univ)⁻¹)

/-- `eq:mo-full-palm` as a probability kernel and its complete Borel
functional formula, in every dimension and at every energy. -/
theorem mixedMaximumPalmKernel_probability_and_formula (n : ℕ) (μ : FiniteMixture)
    {β x Q L R : ℝ} (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    IsMarkovKernel (mixedMaximumPalmKernel n μ Q u hu (Ioo L R)) ∧
      ∀ e : ℝ, ∀ f : Disorder (n+2) μ.maxDegree × ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ w, f w ∂mixedMaximumPalmKernel n μ Q u hu (Ioo L R) e) =
          maximumPalmExpectation n μ Q u hu e (Ioo L R) (fun J k => f (J,k)) := by
  let κ := mixedPalmNumerator n μ Q u hu (Ioo L R)
  have hZpos (e : ℝ) : 0 < sourceRawRadialNormalization n μ Q (Ioo L R) e := by
    have hpos := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm ((n+2:ℕ)*e)
    rw [sourceMaximumEnergyDensity_eq_raw n μ h.overlap_range.1 hnp] at hpos
    exact pos_of_mul_pos_right hpos (sourcePhysicalRadialFactor_pos n μ h.overlap_range.1 hnp).le
  have hmass (e : ℝ) : κ e univ =
      ENNReal.ofReal (sourceRawRadialNormalization n μ Q (Ioo L R) e) := by
    have hnorm := maximumPalmExpectation_one n μ h hnp hL hm u hu e
    have he := mixedPalmNumerator_formula n μ Q u hu (Ioo L R) e (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at he
    have hpos := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm ((n+2:ℕ)*e)
    rw [sourceMaximumEnergyDensity_eq_raw n μ h.overlap_range.1 hnp] at hpos
    have hRpos : 0 < sourceRawRadialNormalization n μ Q (Ioo L R) e :=
      pos_of_mul_pos_right hpos (sourcePhysicalRadialFactor_pos n μ h.overlap_range.1 hnp).le
    unfold maximumPalmExpectation at hnorm
    simp only [mul_one] at hnorm
    change (ENNReal.ofReal (sourceRawRadialNormalization n μ Q (Ioo L R) e))⁻¹ * _ = 1 at hnorm
    change _ = _ at he
    change (ENNReal.ofReal (sourceRawRadialNormalization n μ Q (Ioo L R) e))⁻¹ *
      (∫⁻ k in Ioo L R, ENNReal.ofReal (Real.exp (-(n+2:ℕ)/2*
        scoreQuadratic μ Q (scorePairEquiv (e,k)))) *
          ∫⁻ J, negativeDetWeight n μ Q u J ∂mixedConditionedLaw _ u hu (scorePairEquiv (e,k))) = 1 at hnorm
    rw [← he] at hnorm
    have H := congrArg (fun t => ENNReal.ofReal (sourceRawRadialNormalization n μ Q (Ioo L R) e)*t) hnorm
    simpa only [←mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hRpos)
      ENNReal.ofReal_ne_top, one_mul, mul_one] using H
  have hweight : Measurable (uncurry (fun e (_ : Disorder (n+2) μ.maxDegree × ℝ) =>
      (κ e univ)⁻¹)) := (κ.measurable_coe MeasurableSet.univ).inv.comp measurable_fst
  have hformula (e : ℝ) (f : Disorder (n+2) μ.maxDegree × ℝ → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ w, f w ∂mixedMaximumPalmKernel n μ Q u hu (Ioo L R) e) =
        maximumPalmExpectation n μ Q u hu e (Ioo L R) (fun J k => f (J,k)) := by
    rw [mixedMaximumPalmKernel, Kernel.lintegral_withDensity κ hweight e hf,
      lintegral_const_mul' _ _ (by
        rw [hmass]
        exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (hZpos e))),
      mixedPalmNumerator_formula n μ Q u hu (Ioo L R) e f hf, hmass]
    rfl
  refine ⟨⟨fun e => ⟨?_⟩⟩, hformula⟩
  simpa only [lintegral_one] using
    (hformula e (fun _ => 1) measurable_const).trans
      (maximumPalmExpectation_one n μ h hnp hL hm u hu e)

/-- Exactly (A1)--(A4) of the manuscript, for the bounded open interval
`(L,R)`. The two closure conditions are expressed on `[L,R]`. -/
structure Admissible (μ : FiniteMixture) (β x Q L R δ : ℝ) : Prop where
  edge : sourceRadialEdge μ Q < L
  contact : markK μ β Q ∈ Ioo L R
  width : 0 < δ
  score : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ), ∀ k ∈ Icc L R,
    (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2
  excluded : δ ≤ sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
  saddle : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
    sourceRadialClearance μ β Q (Ioo L R)/2 ≤
      Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ

/-- All four admissibility conditions survive decreasing the energy width. -/
theorem Admissible.shrink_energy {μ : FiniteMixture} {β x Q L R δ δ' : ℝ}
    (hA : Admissible μ β x Q L R δ) (hδ' : 0 < δ') (hle : δ' ≤ δ) :
    Admissible μ β x Q L R δ' := by
  have hs : Icc (markE μ β x Q-δ') (markE μ β x Q+δ') ⊆
      Icc (markE μ β x Q-δ) (markE μ β x Q+δ) := by
    intro e he
    constructor <;> linarith [he.1,he.2]
  exact ⟨hA.edge,hA.contact,hδ',fun e he => hA.score e (hs he),
    hle.trans hA.excluded,fun e he => hA.saddle e (hs he)⟩

/-- Literal admissibility can be imposed inside every supplied exterior
neighborhood, with any supplied upper bound on the energy width. No saddle
clearance or score-band hypothesis is required from the caller. -/
theorem exists_admissible_rectangle (μ : FiniteMixture) {β x Q L₀ R₀ δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : sourceRadialEdge μ Q < L₀) (hm : markK μ β Q ∈ Ioo L₀ R₀)
    (hδMax : 0 < δMax) :
    ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧ δ ≤ δMax ∧ Admissible μ β x Q L R δ := by
  obtain ⟨ρ,hρ,hscore⟩ := source_contact_score_neighborhood μ h hnp
  let L := max ((L₀+markK μ β Q)/2) (markK μ β Q-ρ)
  let R := min ((R₀+markK μ β Q)/2) (markK μ β Q+ρ)
  have hL : L < markK μ β Q := max_lt (by linarith [hm.1]) (by linarith)
  have hR : markK μ β Q < R := lt_min (by linarith [hm.2]) (by linarith)
  have hL₀ : L₀ < L := lt_of_lt_of_le (by linarith [hm.1]) (le_max_left _ _)
  have hR₀ : R < R₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith [hm.2])
  obtain ⟨a,ha,hclear⟩ :=
    SphericalTAPMixedSaddleClearanceChoice.sourceRadialSaddle_nearby_half_clearance μ h hnp ⟨hL,hR⟩
  let d := sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
  have hd : 0 < d := by
    have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
      (by have := h.min_degree; omega) hnp
    have hu := sourceRadialClearance_pos μ (show markK μ β Q ∈ Ioo L R from ⟨hL,hR⟩)
    have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
    dsimp [d]
    positivity
  let δ := min δMax (min ρ (min d a))
  have hδ : 0 < δ := lt_min hδMax (lt_min hρ (lt_min hd ha))
  have hδρ : δ ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hδd : δ ≤ d := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : δ ≤ a := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨L,R,δ,hL₀,hR₀,min_le_left _ _,hEdge.trans hL₀,⟨hL,hR⟩,hδ,?_,hδd,?_⟩
  · intro e he k hk
    apply hscore e k
    · exact abs_le.mpr ⟨by linarith [he.1],by linarith [he.2]⟩
    · have hleft : markK μ β Q-ρ ≤ L := le_max_right _ _
      have hright : R ≤ markK μ β Q+ρ := min_le_right _ _
      exact abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  · intro e he
    exact hclear e ⟨by linarith [he.1],by linarith [he.2]⟩

/-- The radial theorem and all six microscopic conclusions on one literally
admissible neighborhood, chosen before dimensions and fixed windows. This
removes every auxiliary admissibility premise from those existing theorems. -/
theorem mixed_radial_and_microscopic_common (μ : FiniteMixture) {β x Q L₀ R₀ δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : sourceRadialEdge μ Q < L₀) (hm : markK μ β Q ∈ Ioo L₀ R₀)
    (hδMax : 0 < δMax) :
    ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧ δ ≤ δMax ∧
      Admissible μ β x Q L R δ ∧ SourceMarkedRadialConclusions μ β x Q L R δ ∧
      Nonempty (SourceMaximumAllConclusions μ β x Q L R δ) := by
  obtain ⟨L,R,δ,hL,hR,hδ,hA⟩ := exists_admissible_rectangle μ h hnp hEdge hm hδMax
  exact ⟨L,R,δ,hL,hR,hδ,hA,
    sourceMarked_radial_all_conclusions μ h hnp hA.edge hA.contact hA.width hA.score hA.saddle,
    sourceMaximum_all_six_conclusions μ h hnp hA.edge hA.contact hA.width hA.score hA.excluded⟩

/-- The pure raw-energy Kac--Rice coefficient, including the scalar
Jacobian. Multiplying it by the maximum determinant mean gives the printed
one-dimensional maximum intensity. -/
def purePhysicalCoefficient (n : ℕ) (μ : FiniteMixture) (Q H : ℝ) : ℝ≥0∞ :=
  sphereKRPrefactor (n+1) μ Q *
    (ENNReal.ofReal ((n+2:ℕ):ℝ)⁻¹ * physicalValuePdf (n+2) μ Q (H/(n+2:ℕ)))

/-- Arbitrary Borel sets in the raw energy/radial plane and arbitrary
nonnegative whole-disorder/point weights, for the singular pure graph law.
This is a weighted identity, not merely the unweighted count formula. -/
theorem pure_marked_raw_kacRice (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (ψ : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree → Vector (n+2) → ℝ≥0∞)
    (hψ : Measurable (fun z : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree ×
      Vector (n+2) => ψ z.1 z.2)) :
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A) ψ)
      (disorderLaw (n+2) μ.maxDegree) ∧
    (∫⁻ J, actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A) ψ J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
        ∫⁻ H in purePhysicalGraph n p ⁻¹' A, purePhysicalCoefficient n μ Q H *
          (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| * ψ J u
            ∂valueConditionedLaw c u hu (H/(n+2:ℕ)))
      else 0 ∂sphereLaw (n+2) := by
  dsimp only
  have hK : MeasurableSet (purePhysicalScoreSet n A) := hA.preimage (by fun_prop)
  obtain ⟨hm,hkr⟩ := actual_pure_score_window_kacRice (n+1) (by omega) p hp a ha hQ
    (purePhysicalScoreSet n A) hK ψ hψ
  refine ⟨hm,hkr.trans ?_⟩
  rw [←lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) _ Q)]
  apply lintegral_congr
  intro u
  by_cases hu : ‖u‖^2=(n+2:ℕ)
  · simp only [valueWindowIntensity,dite_eq_left hu]
    have hset : pureScoreWindow p (purePhysicalScoreSet n A) =
        (fun e : ℝ => (n+2:ℕ)*e) ⁻¹' (purePhysicalGraph n p ⁻¹' A) := by
      ext e
      change ((n+2:ℕ)*e,(p:ℝ)*e) ∈ A ↔
        ((n+2:ℕ)*e,(p:ℝ)*((n+2:ℕ)*e)/(n+2:ℕ)) ∈ A
      have he : (p:ℝ)*((n+2:ℕ)*e)/(n+2:ℕ) = (p:ℝ)*e := by field_simp
      rw [he]
    rw [hset,setLIntegral_positive_rescale (n+2:ℕ) (by positivity),
      ←lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) _ Q)]
    apply lintegral_congr
    intro H
    simp only [purePhysicalCoefficient,mul_assoc]
  · simp only [valueWindowIntensity,dite_eq_right hu,mul_zero]

/-- The actual pure maximum intensity is the scalar KR coefficient times
the negative-Hessian determinant mean, with no asymptotic prefactor. -/
theorem purePhysicalCoefficient_mul_maximumMean (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) (Q H : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    purePhysicalCoefficient n μ Q H *
      ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*(H/(n+2:ℕ)))) =
        pureLocalMaxPhysicalIntensity n p hp a ha Q H := by
  simp only [purePhysicalCoefficient,pureLocalMaxPhysicalIntensity,pureNegativeIntensity]
  ac_rfl

/-- The pure posterior is a measurable probability kernel in the scalar
energy mark. It conditions on value and tangent gradient only. -/
def purePosteriorKernel (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    Kernel ℝ (Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree) :=
  (coefficientKernel (ValueTangentConditioning.valueTangentCLM
    (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
      u (tangentFrame u hu))).comap
        (fun e => jointValueTarget (n+1) ((n+2:ℕ)*e))
        ((jointValueTarget_continuous (n+1)).measurable.comp (by fun_prop))

instance purePosteriorKernel_markov (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    IsMarkovKernel (purePosteriorKernel n p hp a ha Q u hu) := by
  unfold purePosteriorKernel
  infer_instance

/-- The negative-Hessian weighted pure posterior, carrying the Dirac mark
`k=p*e`. This numerator retains correlation with every whole-field weight. -/
def purePalmNumerator (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    Kernel ℝ (Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × ℝ) :=
  (purePosteriorKernel n p hp a ha Q u hu ×ₖ
    Kernel.deterministic (fun e : ℝ => (p:ℝ)*e) (by fun_prop)).withDensity
      (fun _ z => negativeDetWeight n (FiniteMixture.pure p hp a ha) Q u z.1)

private lemma purePalmNumerator_formula (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q : ℝ) (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (e : ℝ)
    (f : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, f z ∂purePalmNumerator n p hp a ha Q u hu e) =
      ∫⁻ J, negativeDetWeight n (FiniteMixture.pure p hp a ha) Q u J * f (J,(p:ℝ)*e)
        ∂valueConditionedLaw (centerCoefficients
          (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q) u hu e := by
  have hd : Measurable (uncurry (fun (_ : ℝ)
      (z : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × ℝ) =>
        negativeDetWeight n (FiniteMixture.pure p hp a ha) Q u z.1)) :=
    (negativeDetWeight_measurable n _ Q u hu).comp measurable_snd.fst
  rw [purePalmNumerator,Kernel.lintegral_withDensity _ hd _ hf]
  rw [Kernel.lintegral_prod_deterministic (by fun_prop) _ _
    (g := fun z => negativeDetWeight n (FiniteMixture.pure p hp a ha) Q u z.1*f z)
    (((negativeDetWeight_measurable n _ Q u hu).comp measurable_fst).mul hf)]
  rfl

instance purePalmNumerator_sfinite (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q : ℝ) (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    IsSFiniteKernel (purePalmNumerator n p hp a ha Q u hu) := by
  unfold purePalmNumerator
  apply Kernel.IsSFiniteKernel.withDensity
  intro e z
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  unfold negativeHessianMark
  split_ifs <;> simp

/-- The pure Palm kernel, measurable in energy; its restriction to `p*e>0`
is a probability kernel and agrees exactly with `mo-pure-palm`. -/
def pureMaximumPalmKernel (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q : ℝ) (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    Kernel ℝ (Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × ℝ) :=
  (purePalmNumerator n p hp a ha Q u hu).withDensity
    (fun e _ => (purePalmNumerator n p hp a ha Q u hu e univ)⁻¹)

/-- The scalar graph Palm measure is a measurable kernel, with its full
Borel test formula and probability normalization on the exterior support. -/
theorem pureMaximumPalmKernel_eq_and_probability (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (e : ℝ) (he : 0 < (p:ℝ)*e) :
    pureMaximumPalmKernel n p hp a ha Q u hu e = pureMaximumPalm n p hp a ha Q e u hu ∧
      IsProbabilityMeasure (pureMaximumPalmKernel n p hp a ha Q u hu e) := by
  let μ := FiniteMixture.pure p hp a ha
  let κ := purePalmNumerator n p hp a ha Q u hu
  let M := ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e))
  have hM : M ≠ 0 := (ENNReal.ofReal_pos.mpr (maximumMean_pos_all_dimensions n (by omega)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) he)).ne'
  have hmass : κ e univ = M := by
    have ht := purePalmNumerator_formula n p hp a ha Q u hu e (fun _ => 1) measurable_const
    simp only [lintegral_one,mul_one] at ht
    exact ht.trans (pure_posterior_negative_det_mean n p hp a ha hQ u hu e)
  have hweight : Measurable (uncurry (fun e (_ : Disorder (n+2) μ.maxDegree × ℝ) =>
      (κ e univ)⁻¹)) := (κ.measurable_coe MeasurableSet.univ).inv.comp measurable_fst
  have hEq : pureMaximumPalmKernel n p hp a ha Q u hu e = pureMaximumPalm n p hp a ha Q e u hu := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [pureMaximumPalmKernel,Kernel.lintegral_withDensity κ hweight e hf,
      lintegral_const_mul' _ _ (by rw [hmass]; exact ENNReal.inv_ne_top.mpr hM),
      purePalmNumerator_formula n p hp a ha Q u hu e f hf,hmass,
      (pureMaximumPalm_probability_and_formula n p hp a ha hQ e he u hu).2 f hf]
    change M⁻¹ * _ = _ / M
    rw [div_eq_mul_inv,mul_comm]
    rfl

  refine ⟨hEq,?_⟩
  rw [hEq]
  exact (pureMaximumPalm_probability_and_formula n p hp a ha hQ e he u hu).1

/-- Full weighted pure maximum-count/Palm disintegration on every Borel
raw mark set in the positive exterior half-plane. Arbitrary field/point
weights include the manuscript's whole-field/radial test functions. -/
theorem pure_weighted_maximum_palm_disintegration (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z.2)
    (ψ : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree → Vector (n+2) → ℝ≥0∞)
    (hψ : Measurable (fun z : Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree ×
      Vector (n+2) => ψ z.1 z.2)) :
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A)
      (fun J u => negativeHessianMark (n+1) c J u * ψ J u) J
        ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
        ∫⁻ H in purePhysicalGraph n p ⁻¹' A, pureLocalMaxPhysicalIntensity n p hp a ha Q H *
          (∫⁻ z, ψ z.1 u ∂pureMaximumPalmKernel n p hp a ha Q u hu (H/(n+2:ℕ)))
      else 0 ∂sphereLaw (n+2) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  rw [(pure_marked_raw_kacRice n p hp a ha hQ A hA
    (fun J u => negativeHessianMark (n+1) c J u*ψ J u)
    ((negativeHessianMark_measurable (n+1) c).mul hψ)).2]
  apply lintegral_congr
  intro u
  by_cases hu : ‖u‖^2=(n+2:ℕ)
  · simp only [dite_eq_left hu]
    apply lintegral_congr_ae
    have hg : Measurable (purePhysicalGraph n p) := by unfold purePhysicalGraph; fun_prop
    filter_upwards [ae_restrict_mem (hA.preimage hg)] with H hH
    have he : 0 < (p:ℝ)*(H/(n+2:ℕ)) := by
      have ht := hpos _ hH
      change 0 < (p:ℝ)*H/(n+2:ℕ) at ht
      convert ht using 1
      ring
    let M := ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*(H/(n+2:ℕ))))
    have hM : M ≠ 0 := (ENNReal.ofReal_pos.mpr (maximumMean_pos_all_dimensions n (by omega)
      (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) he)).ne'
    have hf : Measurable (fun z : Disorder (n+2) μ.maxDegree × ℝ => ψ z.1 u) :=
      hψ.comp (measurable_fst.prodMk measurable_const)
    rw [(pureMaximumPalmKernel_eq_and_probability n p hp a ha hQ u hu _ he).1,
      (pureMaximumPalm_probability_and_formula n p hp a ha hQ _ he u hu).2 _ hf,
      ←purePhysicalCoefficient_mul_maximumMean n p hp a ha Q H]
    change _ = (purePhysicalCoefficient n μ Q H*M)*(_/M)
    have hcancel (b : ℝ≥0∞) : M*(b/M)=b := by
      rw [div_eq_mul_inv,mul_comm b,←mul_assoc,
        ENNReal.mul_inv_cancel hM ENNReal.ofReal_ne_top,one_mul]
    rw [mul_assoc,hcancel]
    apply congrArg (fun t => purePhysicalCoefficient n μ Q H*t)
    apply lintegral_congr
    intro J
    simp only [mul_assoc]
    rfl
  · simp only [dite_eq_right hu]

/-- The complete all-high event on fixed constants and a fixed radial
interval. Its energy cutoff and whole-sphere third derivative are explicit. -/
def AllHighOn (μ : FiniteMixture) (β x Q κ C L R δ : ℝ) : Prop :=
  ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
    ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
      (∀ n, MeasurableSet (Ω n)) ∧
      (∀ n, (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ A*Real.exp (-c*(n+2:ℕ))) ∧
      ∀ n J, J ∈ Ω n →
        sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J ≤ C ∧
        (∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
          ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖ ≤
            C/Real.sqrt (n+2:ℕ)) ∧
        ∀ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) →
          surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 →
          (n+2:ℕ)*(markE μ β x Q-δ) ≤
            field (centerCoefficients (mixtureCoefficients μ) Q) J u →
          field (centerCoefficients (mixtureCoefficients μ) Q) J u ≤
            (n+2:ℕ)*(markE μ β x Q+δ) ∧
          actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R ∧
          sourceHessianMargin (centerCoefficients (mixtureCoefficients μ) Q) κ J u

/-- Posterior exclusion, ordinary relative determinant loss, and the
nonnegative retained-weight lower bound, all on exactly the same event. -/
def MixedFilterOn (μ : FiniteMixture) (β x Q κ C ε η L R δ : ℝ) : Prop :=
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  ∃ c A B : ℝ, 0 < c ∧ 0 < A ∧ 0 < B ∧
    ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
      ∀ e ∈ Icc (E-δ) (E+δ), ∀ k ∈ Icc L R,
        let cQ := centerCoefficients (mixtureCoefficients μ) Q
        let ν := mixedConditionedLaw cQ u hu (scorePairEquiv (e,k))
        ν.real {J | ¬sourceSelectionEvent cQ κ C ε η E G J u} ≤ A*Real.exp (-c*(n+2:ℕ)) ∧
        (∫ J in {J | ¬sourceSelectionEvent cQ κ C ε η E G J u}, intrinsicDet μ Q u J ∂ν) ≤
          B*Real.exp (-(c/2)*(n+2:ℕ))*(∫ J, intrinsicDet μ Q u J ∂ν) ∧
        ENNReal.ofReal (1-B*Real.exp (-(c/2)*(n+2:ℕ)))*
          (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤
            ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*
              sourceSelectionMark cQ κ C ε η E G J u ∂ν

private theorem margin_mono {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (u : Vector N) {κ κ' : ℝ} (hle : κ ≤ κ') (h : sourceHessianMargin c κ' J u) :
    sourceHessianMargin c κ J u := by
  intro v
  exact (h v).trans (by nlinarith [sq_nonneg ‖tangentProjection u v‖,
    mul_le_mul_of_nonneg_right hle (sq_nonneg ‖tangentProjection u v‖)])

private theorem failure_rate_exponential (μ : FiniteMixture) {Q G g : ℝ}
    (hQ : 0 < Q) (hG : 0 < G) (hg : 0 < g) (grid : ℕ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ n : ℕ,
      sourceSelectionFailureRate μ Q G g grid n ≤ A*Real.exp (-c*(n+2:ℕ)) := by
  let a := ((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2)
  let b := (G/8)^2/(2*μ.xi Q)
  have hbQ : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; have hξ := μ.xi_pos hQ; positivity
  let c := min (1/2) (min (a/2) b)
  let A := 2*(Fintype.card (Degree μ.maxDegree):ℝ)+1+(grid+1:ℕ)
  refine ⟨c,A,lt_min (by norm_num) (lt_min (by positivity) hb),by dsimp [A]; positivity,?_⟩
  intro n
  have hc1 : c ≤ 1/2 := min_le_left _ _
  have hca : c ≤ a/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have h1 : Real.exp (-(n+2:ℕ)/2) ≤ Real.exp (-c*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc1 (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
  have h2 : Real.exp (-(n+1:ℝ)*a) ≤ Real.exp (-c*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_right hca (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
  have h3 : Real.exp (-(n+2:ℕ)*b) ≤ Real.exp (-c*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb (show (0:ℝ) ≤ (n+2:ℕ) by positivity)]
  unfold sourceSelectionFailureRate
  rw [show -(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2) =
    -(n+1:ℝ)*a by dsimp [a]; ring,
    show -(n+2:ℕ)*(G/8)^2/(2*μ.xi Q) = -(n+2:ℕ)*b by dsimp [b]; ring]
  calc
    _ ≤ 2*(Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-c*(n+2:ℕ))+
        Real.exp (-c*(n+2:ℕ))+(grid+1:ℕ)*Real.exp (-c*(n+2:ℕ)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) h2)
        (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem mixed_filter_from_probability (μ : FiniteMixture)
    {β x Q κ C ε η L R δ g c A : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hg : 0 < g) (hL : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ L)
    (hc : 0 < c) (hA : 0 < A)
    (hprob : ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
      ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ), ∀ k ∈ Icc L R,
        (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
          (scorePairEquiv (e,k))).real {J | ¬sourceSelectionEvent
            (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η (markE μ β x Q)
              (gap μ Q (markY β Q) (markZ x Q) ε η) J u} ≤ A*Real.exp (-c*(n+2:ℕ))) :
    MixedFilterOn μ β x Q κ C ε η L R δ := by
  obtain ⟨C₂,hC₂,hmom⟩ := mixed_conditioned_determinant_moments μ h.overlap_range.1 hnp
    (g:=g) (Z:=R) (r:=2) hg (by norm_num)
  let B := Real.sqrt C₂*Real.sqrt A
  have hB : 0 < B := by dsimp [B]; positivity
  have hs (n : ℕ) : Real.sqrt C₂*Real.sqrt (A*Real.exp (-c*(n+2:ℕ))) =
      B*Real.exp (-(c/2)*(n+2:ℕ)) := by
    have he : Real.sqrt (Real.exp (-c*(n+2:ℕ))) = Real.exp (-(c/2)*(n+2:ℕ)) := by
      rw [Real.sqrt_eq_rpow,←Real.exp_mul]
      congr 1
      ring
    rw [Real.sqrt_mul hA.le,he]
    dsimp [B]
    ring
  have ht : Tendsto (fun n : ℕ => B*Real.exp (-(c/2)*(n+2:ℕ))) atTop (𝓝 0) := by
    have H := (source_dimension_exp_tail_tendsto 2 (half_pos hc)).const_mul B
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  refine ⟨c,A,B,hc,hA,hB,?_⟩
  filter_upwards [hprob,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn herr
  intro u hu e he k hk
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let ν := mixedConditionedLaw cQ u hu (scorePairEquiv (e,k))
  let : IsProbabilityMeasure ν := by unfold ν mixedConditionedLaw; infer_instance
  let S := {J : Disorder (n+2) μ.maxDegree | sourceSelectionEvent cQ κ C ε η
    (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η) J u}
  have hS : MeasurableSet S := by
    change MeasurableSet ((fun J : Disorder (n+2) μ.maxDegree => (J,u)) ⁻¹'
      {p : Disorder (n+2) μ.maxDegree × Vector (n+2) | sourceSelectionEvent cQ κ C ε η
        (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η) p.1 p.2})
    exact (sourceSelectionEvent_measurable (N:=n+2) (P:=μ.maxDegree) cQ κ C ε η
      (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η)).preimage
        (measurable_id.prodMk measurable_const)
  have hfail := hn u hu e he k hk
  obtain ⟨hD,_hMean,hm,hMom,hMC⟩ := hmom n u hu (scorePairEquiv (e,k)) (hL.trans hk.1) hk.2
  refine ⟨hfail,?_,?_⟩
  · have H := determinant_event_holder ν (intrinsicDet μ Q u) hD
      (.of_forall (fun _ => abs_nonneg _)) hm Sᶜ hS.compl hMom hMC hfail
    rw [hs n] at H
    exact (div_le_iff₀ hm).mp H
  · have H := sourceDeterminant_retained_weight_lower ν (intrinsicDet μ Q u) S hS hD
      (.of_forall (fun _ => abs_nonneg _)) hm hMom hMC hfail (by rw [hs n]; exact herr.le)
    rw [hs n] at H
    have heq : S.indicator (fun _ => (1:ℝ≥0∞)) =
        fun J => sourceSelectionMark cQ κ C ε η (markE μ β x Q)
          (gap μ Q (markY β Q) (markZ x Q) ε η) J u := by
      funext J
      by_cases hJ : J ∈ S
      · rw [indicator_of_mem hJ]
        change (1:ℝ≥0∞) = if J ∈ S then 1 else 0
        rw [ite_eq_left hJ]
      · rw [indicator_of_notMem hJ]
        change (0:ℝ≥0∞) = if J ∈ S then 1 else 0
        rw [ite_eq_right hJ]
    rw [heq] at H
    exact H

/-- A single pre-dimension witness for the mixed one-point interface.
The same κ, regularity cutoff, exact collar, admissible mark rectangle and
unit-tail center support localization, the filter, determinant loss, the
radial theorem and all six microscopic conclusions. -/
theorem mixed_onePoint_common_witness (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : sourceRadialEdge μ Q < L₀)
    (hm : markK μ β Q ∈ Ioo L₀ R₀) :
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧
          δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          Admissible μ β x Q L R δ ∧
          AllHighOn μ β x Q κ C L R δ ∧
          MixedFilterOn μ β x Q κ C ε η L R δ ∧
          SourceMarkedRadialConclusions μ β x Q L R δ ∧
          Nonempty (SourceMaximumAllConclusions μ β x Q L R δ) := by
  let κ := (L₀-sourceRadialEdge μ Q)/4
  have hκ : 0 < κ := div_pos (sub_pos.mpr hEdge) (by norm_num)
  obtain ⟨C₀,_hκ₀,hC₀,_hη₀,_hη₀one,hhigh⟩ := mixed_all_high_literal μ h hnp hEdge hm.1 hm.2
  let E := markE μ β x Q
  let g := (markK μ β Q-sourceRadialEdge μ Q)/2
  let a₀ := sourceRadialEdge μ Q+g
  let b₀ := markK μ β Q+1
  let M := |E|+1+|a₀|+|b₀|+1
  have hg : 0 < g := by
    have H := sourceContact_markK_above_edge μ h
    dsimp [g,sourceRadialEdge]
    exact div_pos (sub_pos.mpr H) (by norm_num)
  obtain ⟨C₁,hC₁,hreg⟩ := source_mixed_physical_posterior_sphere_regularity μ h.overlap_range.1 hnp
    (show 0 ≤ M by dsimp [M]; positivity)
  let C := max C₀ C₁
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
  have hθ : 0 < min (Real.pi/4) (κ/(2*C)) := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ : min (Real.pi/4) (κ/(2*C)) < Real.pi/2 :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (min (Real.pi/4) (κ/(2*C))) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθπ⟩
  have hcos1 : Real.cos (min (Real.pi/4) (κ/(2*C))) < 1 := by
    have H := Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=min (Real.pi/4) (κ/(2*C)))
      (by norm_num) (by linarith [Real.pi_pos]) hθ
    simpa only [Real.cos_zero] using H
  have hη : 0 < η := sub_pos.mpr hcos1
  refine ⟨C,hκ,hC,hη,by linarith,?_⟩
  intro ε hε hεη
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hG : 0 < G := (source_trial_gap μ h hnp hε hη hεη).1
  have hregC : ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
      ∀ e k : ℝ, |e| ≤ M → |k| ≤ M →
        (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
          (WithLp.toLp 2 ![e,k])).real {J | C < sourceSphereRegularity
            (centerCoefficients (mixtureCoefficients μ) Q) J} ≤
              (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2) := by
    intro n u hu e k he hk
    let ν := mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (WithLp.toLp 2 ![e,k])
    let : IsProbabilityMeasure ν := by unfold ν mixedConditionedLaw; infer_instance
    exact (measureReal_mono (fun J hJ => lt_of_le_of_lt (le_max_right C₀ C₁) hJ)).trans
      (hreg n u hu e k he hk)
  obtain ⟨Lf,Rf,δf,hLf,hRf,hsub,hδf,hδG,hδfone,grid,_hgrid,hprob⟩ :=
    source_mixed_physical_posterior_selection_failure_fixed_regularity μ h hnp hε hη hεη
      (by norm_num : (0:ℝ)<1) hC (show |E|+1+|a₀|+|b₀|+1 ≤ M from le_rfl) hregC
  let Lb := max Lf ((L₀+markK μ β Q)/2)
  let Rb := min Rf ((R₀+markK μ β Q)/2)
  have hLb : Lb < markK μ β Q := max_lt hLf (by linarith [hm.1])
  have hRb : markK μ β Q < Rb := lt_min hRf (by linarith [hm.2])
  have hL₀b : L₀ < Lb := lt_of_lt_of_le (by linarith [hm.1]) (le_max_right _ _)
  have hRb₀ : Rb < R₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith [hm.2])
  obtain ⟨L,R,δa,hLbL,hRRb,hδaf,hAd⟩ := exists_admissible_rectangle μ h hnp
    (hEdge.trans hL₀b) ⟨hLb,hRb⟩ hδf
  obtain ⟨δU,hδU,_hδUone,hAll⟩ := hhigh L R (hL₀b.trans hLbL) (hRRb.trans hRb₀)
    hAd.contact.1 hAd.contact.2
  let δ := min δa δU
  have hδ : 0 < δ := lt_min hAd.width hδU
  have hδa : δ ≤ δa := min_le_left _ _
  have hAf := hAd.shrink_energy hδ hδa
  obtain ⟨c,A,hc,hA,hrate⟩ := failure_rate_exponential μ h.overlap_range.1 hG hg grid
  have hLfL : Lf ≤ L := (le_max_left _ _).trans hLbL.le
  have hRRf : R ≤ Rf := hRRb.le.trans (min_le_left _ _)
  have hκg : κ ≤ g/2 := by dsimp [κ,g]; linarith [hm.1]
  have hpost : ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
      ∀ e ∈ Icc (E-δ) (E+δ), ∀ k ∈ Icc L R,
        (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
          (scorePairEquiv (e,k))).real {J | ¬sourceSelectionEvent
            (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u} ≤ A*Real.exp (-c*(n+2:ℕ)) := by
    filter_upwards [hprob] with n hn
    intro u hu e he k hk
    let ν := mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e,k))
    let : IsProbabilityMeasure ν := by unfold ν mixedConditionedLaw; infer_instance
    have hbox := filter_box_shrinking hLfL hRRf (hδa.trans hδaf) he hk
    have hfail := hn u hu e hbox.1 k hbox.2
    have hsubJ : {J : Disorder (n+2) μ.maxDegree | ¬sourceSelectionEvent
        (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u} ⊆
      {J | ¬sourceSelectionEvent (centerCoefficients (mixtureCoefficients μ) Q)
        (g/2) C ε η E G J u} := by
      intro J hJ hs
      exact hJ ⟨margin_mono _ J u hκg hs.1,hs.2⟩
    have hb : ν.real {J | ¬sourceSelectionEvent (centerCoefficients (mixtureCoefficients μ) Q)
        κ C ε η E G J u} ≤ ν.real {J | ¬sourceSelectionEvent
          (centerCoefficients (mixtureCoefficients μ) Q) (g/2) C ε η E G J u} :=
      measureReal_mono hsubJ
    exact hb.trans (hfail.trans (hrate n))
  have hgapL : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ L := by
    have H := hsub (show Lf ∈ Icc Lf Rf from ⟨le_rfl,hLf.le.trans hRf.le⟩)
    exact H.1.le.trans hLfL
  refine ⟨L,R,δ,hL₀b.trans hLbL,hRRb.trans hRb₀,(hδa.trans hδaf).trans_lt hδG,hAf,?_,
    mixed_filter_from_probability μ h hnp hg hgapL hc hA hpost,
    sourceMarked_radial_all_conclusions μ h hnp hAf.edge hAf.contact hδ hAf.score hAf.saddle,
    sourceMaximum_all_six_conclusions μ h hnp hAf.edge hAf.contact hδ hAf.score hAf.excluded⟩
  obtain ⟨ch,Ah,hch,hAh,Ω,hΩm,hΩ,hΩp⟩ := hAll δ hδ (min_le_right _ _)
  refine ⟨ch,Ah,hch,hAh,Ω,hΩm,hΩp,?_⟩
  intro n J hJ
  obtain ⟨hregJ,hthird,_hSup,hcrit⟩ := hΩ n J hJ
  refine ⟨hregJ.trans (le_max_left _ _),?_,?_⟩
  · intro u hu
    exact (hthird u hu).trans (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · intro u hu huc hhighu
    exact ⟨(hcrit u hu huc hhighu).1,(hcrit u hu huc hhighu).2.1,(hcrit u hu huc hhighu).2.2.1⟩

private theorem mixedConditioned_critical_ae (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂mixedConditionedLaw c u hu z, surfaceGradient (field c J) u=0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have H := coefficientKernel_observation_ae (jointCLM c u (tangentFrame u hu))
    (center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z))
  filter_upwards [H] with J hJ
  have hg : gradientCLM c u (tangentFrame u hu) (euclideanDisorder J)=0 := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun v => v (Sum.inr i)) hJ
    simpa only [actualObservation,jointCLM_apply_inr,jointScoreTarget,WithLp.toLp_ofLp,Sum.elim_inr,PiLp.zero_apply] using hi
  have hi := (tangentFrame_gradient_zero_iff c u hu _).mp hg
  have hv := congrArg (fun v : tangentPlane u => (v : Vector (n+2))) hi
  simpa only [IntrinsicGradientRegression.intrinsicGamma_coe (by omega) c u hu,
    unpack_euclideanDisorder,Submodule.coe_zero] using hv

/-- The literal spatially averaged retained negative-determinant numerator
in the mixed intensity. -/
def mixedRetainedDeterminantMass (n : ℕ) (μ : FiniteMixture) (Q κ C ε η E G e k : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
    ∫⁻ J, negativeDetWeight n μ Q u J *
      sourceSelectionMark (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u
      ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e,k))
  else 0 ∂sphereLaw (n+2)

/-- The retained physical intensity, with the literal coarse mark clipping
and the same Gaussian/Kac--Rice prefactor as the maximum intensity. -/
def mixedRetainedPhysicalIntensity (n : ℕ) (μ : FiniteMixture)
    (Q L R δ κ C ε η E G H k : ℝ) : ℝ≥0∞ :=
  if H/(n+2:ℕ) ∈ Icc (E-δ) (E+δ) ∧ k ∈ Icc L R then
    (ENNReal.ofReal ((n+2:ℕ):ℝ)⁻¹ *
      (sphereKRPrefactor (n+1) μ Q * physicalScorePdf (n+2) μ Q
        (scorePairEquiv (H/(n+2:ℕ),k)))) *
          mixedRetainedDeterminantMass n μ Q κ C ε η E G (H/(n+2:ℕ)) k
  else 0

/-- The deficit of the actual retained intensity relative to the maximum
intensity, uniformly throughout the closed coarse mark rectangle. -/
def MixedRetainedRatioOn (μ : FiniteMixture) (β x Q κ C ε η L R δ : ℝ) : Prop :=
  ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ), ∀ k ∈ Icc L R,
      let ratio := (mixedRetainedPhysicalIntensity n μ Q L R δ κ C ε η (markE μ β x Q)
        (gap μ Q (markY β Q) (markZ x Q) ε η) ((n+2:ℕ)*e) k).toReal /
          (mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k).toReal
      0 ≤ 1-ratio ∧ 1-ratio ≤ B*Real.exp (-c*(n+2:ℕ))

private theorem mixed_ratio_of_filter (μ : FiniteMixture) {β x Q κ C ε η L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (hκ : 0 < κ)
    (hA : Admissible μ β x Q L R δ) (hF : MixedFilterOn μ β x Q κ C ε η L R δ) :
    MixedRetainedRatioOn μ β x Q κ C ε η L R δ := by
  obtain ⟨c,A,B,hc,_hA,hB,hpost⟩ := hF
  let g := (L-sourceRadialEdge μ Q)/2
  have hg : 0 < g := div_pos (sub_pos.mpr hA.edge) (by norm_num)
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hcomp := maximumMean_comparison_eventually (Z:=R) hb hg
  have htail : Tendsto (fun n : ℕ => B*Real.exp (-(c/2)*(n+2:ℕ))) atTop (𝓝 0) := by
    have H := (source_dimension_exp_tail_tendsto 2 (half_pos hc)).const_mul B
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  refine ⟨B,c/2,hB,half_pos hc,?_⟩
  filter_upwards [hpost,hcomp,htail.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn hcompN herr
  intro e he k hk
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let D := mixedRetainedDeterminantMass n μ Q κ C ε η E G e k
  let M := maximumMean n (n+2) (Q^2*μ.xi2 Q) k
  let t := B*Real.exp (-(c/2)*(n+2:ℕ))
  have hkpos : 0 < k := (show 0 ≤ sourceRadialEdge μ Q by unfold sourceRadialEdge; positivity).trans_lt
    (hA.edge.trans_le hk.1)
  have hM : 0 < M := maximumMean_pos_all_dimensions n (by omega) hb hkpos
  have hMk : M ≤ GOEPhysicalPotential.physicalMean n (n+2) (Q^2*μ.xi2 Q) k :=
    (hcompN k ⟨by dsimp [g,sourceRadialEdge] at hg ⊢; linarith [hk.1,hA.edge],hk.2⟩).2
  have hUpper : D ≤ ENNReal.ofReal M := by
    dsimp only [D,mixedRetainedDeterminantMass]
    calc
      _ ≤ ∫⁻ _u : Vector (n+2), ENNReal.ofReal M ∂sphereLaw (n+2) := by
        apply lintegral_mono_ae
        filter_upwards [sphereLaw_support (by omega : 1 ≤ n+2)] with u hu
        rw [dite_eq_left hu]
        apply (lintegral_mono (fun J => mul_le_of_le_one_right zero_le
          (sourceSelectionMark_le_one _ κ C ε η E G J u))).trans_eq
        exact mixed_posterior_negative_det_mean n μ h.overlap_range.1 hnp u hu (scorePairEquiv (e,k))
      _ = _ := by simp
  have hLower : ENNReal.ofReal (1-t)*ENNReal.ofReal M ≤ D := by
    calc
      _ = ∫⁻ _u : Vector (n+2), ENNReal.ofReal (1-t)*ENNReal.ofReal M ∂sphereLaw (n+2) := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [sphereLaw_support (by omega : 1 ≤ n+2)] with u hu
        rw [dite_eq_left hu]
        have hW := (hn u hu e he k hk).2.2
        have hSel : (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*sourceSelectionMark
            (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u
            ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e,k))) =
          ∫⁻ J, negativeDetWeight n μ Q u J*sourceSelectionMark
            (centerCoefficients (mixtureCoefficients μ) Q) κ C ε η E G J u
            ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e,k)) := by
          apply lintegral_congr_ae
          filter_upwards [mixedConditioned_critical_ae n μ h.overlap_range.1 hnp u hu (scorePairEquiv (e,k))]
            with J hJ
          unfold negativeDetWeight intrinsicDet
          rw [mul_assoc,sourceSelectionMark_negative_factor (n+1) _ hκ C ε η E G J u hu hJ]
        rw [←hSel]
        apply le_trans _ hW
        unfold intrinsicDet
        rw [mixed_posterior_det_mean n μ h.overlap_range.1 hnp u hu (scorePairEquiv (e,k))]
        exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hMk) zero_le
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hUpper
  have huR : D.toReal ≤ M := by
    have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUpper
    simpa only [ENNReal.toReal_ofReal hM.le] using H
  have hlR : (1-t)*M ≤ D.toReal := by
    have H := ENNReal.toReal_mono hDtop hLower
    have htn : 0 ≤ 1-t := sub_nonneg.mpr herr.le
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal htn,
      ENNReal.toReal_ofReal hM.le] using H
  have hratio : (mixedRetainedPhysicalIntensity n μ Q L R δ κ C ε η E G ((n+2:ℕ)*e) k).toReal /
      (mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k).toReal = D.toReal/M := by
    have heq : ((n+2:ℕ)*e)/(n+2:ℕ)=e := by field_simp
    let P := ENNReal.ofReal ((n+2:ℕ):ℝ)⁻¹ *
      (sphereKRPrefactor (n+1) μ Q * physicalScorePdf (n+2) μ Q (scorePairEquiv (e,k)))
    have hret : mixedRetainedPhysicalIntensity n μ Q L R δ κ C ε η E G ((n+2:ℕ)*e) k=P*D := by
      rw [mixedRetainedPhysicalIntensity,heq,ite_eq_left ⟨he,hk⟩]
    have hmax : mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k=P*ENNReal.ofReal M := by
      simp only [mixedLocalMaxPhysicalIntensity,mixedNegativeIntensity,heq]
      dsimp [P,M]
      rw [scorePairEquiv_apply]
      ac_rfl
    have hP : 0 < P.toReal := by
      dsimp [P]
      rw [ENNReal.toReal_mul,ENNReal.toReal_mul]
      have hpref := ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ h.overlap_range.1)
        (sphereKRPrefactor_ne_top (n+1) μ Q)
      have hpdf := physicalScorePdf_toReal_pos (n+2) (by omega) μ h.overlap_range.1 hnp (scorePairEquiv (e,k))
      rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ ((n+2:ℕ):ℝ)⁻¹)]
      positivity
    rw [hret,hmax,(ENNReal.toReal_mul (a:=P) (b:=D)),(ENNReal.toReal_mul (a:=P) (b:=ENNReal.ofReal M)),
      ENNReal.toReal_ofReal hM.le]
    exact mul_div_mul_left _ _ hP.ne'
  change 0 ≤ 1-_ ∧ 1-_ ≤ t
  rw [hratio]
  constructor
  · exact sub_nonneg.mpr ((div_le_one hM).mpr huR)
  · have H := (le_div_iff₀ hM).mpr hlR
    linarith

/-- The common mixed witness also has the manuscript's actual retained
intensity ratio. There is no first-moment, filter, or admissibility premise. -/
theorem mixed_onePoint_common_witness_with_ratio (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : sourceRadialEdge μ Q < L₀) (hm : markK μ β Q ∈ Ioo L₀ R₀) :
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧
          δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          Admissible μ β x Q L R δ ∧ AllHighOn μ β x Q κ C L R δ ∧
          MixedFilterOn μ β x Q κ C ε η L R δ ∧
          MixedRetainedRatioOn μ β x Q κ C ε η L R δ ∧
          SourceMarkedRadialConclusions μ β x Q L R δ ∧
          Nonempty (SourceMaximumAllConclusions μ β x Q L R δ) := by
  obtain ⟨C,hκ,hC,hη,hηone,hcommon⟩ := mixed_onePoint_common_witness μ h hnp hEdge hm
  refine ⟨C,hκ,hC,hη,hηone,?_⟩
  intro ε hε hεη
  obtain ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,hRad,hMicro⟩ := hcommon ε hε hεη
  exact ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,mixed_ratio_of_filter μ h hnp hκ hA hF,hRad,hMicro⟩

/-- The full weighted mixed maximum-count/Palm identity, in raw energy.
The sphere integral is placed first as in the repository's Kac--Rice formula;
the energy integrand is the physical intensity times the probability Palm
kernel, and its normalization uses the raw radial mass. -/
theorem mixed_weighted_maximum_palm_disintegration (n : ℕ) (μ : FiniteMixture)
    {β x Q L R : ℝ} (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ψ : Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ≥0∞)
    (hψ : Measurable (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) => ψ z.1 z.2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c
      (physicalEnergyWindow (n+2) B (Ioo L R))
      (fun J u => negativeHessianMark (n+1) c J u*ψ J u) J
        ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u, if hu : ‖u‖^2=(n+2:ℕ) then
        ∫⁻ H in B, ENNReal.ofReal (sourceMaximumEnergyDensity n μ Q (Ioo L R) H) *
          (∫⁻ z, ψ z.1 u ∂mixedMaximumPalmKernel n μ Q u hu (Ioo L R) (H/(n+2:ℕ)))
      else 0 ∂sphereLaw (n+2) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hKR := (marked_raw_kacRice n μ h.overlap_range.1 hnp (B ×ˢ Ioo L R)
    (hB.prod measurableSet_Ioo) (fun J u => negativeHessianMark (n+1) c J u*ψ J u)
      ((negativeHessianMark_measurable (n+1) c).mul hψ)).2
  change (∫⁻ J, actualScoreWindowCount (n+1) c
    {z : EuclideanSpace ℝ (Fin 2) | ((n+2:ℕ)*z 0,z 1) ∈ B ×ˢ Ioo L R}
      (fun J u => negativeHessianMark (n+1) c J u*ψ J u) J ∂disorderLaw (n+2) μ.maxDegree) = _
  rw [hKR]
  apply lintegral_congr
  intro u
  by_cases hu : ‖u‖^2=(n+2:ℕ)
  · simp only [dite_eq_left hu]
    let T : ℝ × ℝ → ℝ × ℝ := fun z => (z.1/(n+2:ℕ),z.2)
    have hT : Measurable T := by fun_prop
    have hp : Measurable (fun J : Disorder (n+2) μ.maxDegree => ψ J u) :=
      hψ.comp (measurable_id.prodMk measurable_const)
    have hn : Measurable (fun z : ℝ × ℝ => ∫⁻ J, negativeDetWeight n μ Q u J*ψ J u
        ∂mixedConditionedLaw c u hu (scorePairEquiv (T z))) :=
      (((negativeDetWeight_measurable n μ Q u hu).mul hp).lintegral_kernel
        (κ:=mixedPosteriorKernel n μ Q u hu)).comp hT
    have hq : Measurable (fun z : ℝ × ℝ => scoreQuadratic μ Q (scorePairEquiv (T z))) := by
      change Measurable (fun z : ℝ × ℝ => scoreQuadratic μ Q (scorePairEquiv ((T z).1,(T z).2)))
      simp_rw [source_scoreQuadratic_precision_form]
      fun_prop
    have hi : Measurable (fun z : ℝ × ℝ =>
        ENNReal.ofReal (mathfrakC n μ Q*Real.exp (-(n+2:ℕ)/2*
          scoreQuadratic μ Q (scorePairEquiv (T z))))) := by fun_prop
    have hInt : Measurable (fun z : ℝ × ℝ =>
        ENNReal.ofReal (mathfrakC n μ Q*Real.exp (-(n+2:ℕ)/2*
          scoreQuadratic μ Q (scorePairEquiv (T z)))) *
            ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
              (negativeHessianMark (n+1) c J u*ψ J u)
                ∂mixedConditionedLaw c u hu (scorePairEquiv (T z))) := by
      have H := hi.mul hn
      convert H using 1
      funext z
      congr 1
      apply lintegral_congr
      intro J
      simp only [negativeDetWeight,mul_assoc]
      rfl
    rw [show StrongFieldComplexity.planeVolume = (volume : Measure ℝ).prod volume from rfl,
      setLIntegral_prod _ hInt.aemeasurable]
    apply lintegral_congr
    intro H
    have hc : 0 < mathfrakC n μ Q := sourcePhysicalRadialFactor_pos n μ h.overlap_range.1 hnp
    have hd : sourceMaximumEnergyDensity n μ Q (Ioo L R) H =
        mathfrakC n μ Q*sourceRawRadialNormalization n μ Q (Ioo L R) (H/(n+2:ℕ)) := by
      have ht := sourceMaximumEnergyDensity_eq_raw n μ h.overlap_range.1 hnp (Ioo L R) (H/(n+2:ℕ))
      have heq : (n+2:ℕ)*(H/(n+2:ℕ))=H := by field_simp
      simpa only [heq,sourcePhysicalRadialFactor,mathfrakC] using ht
    have hZ : 0 < sourceRawRadialNormalization n μ Q (Ioo L R) (H/(n+2:ℕ)) := by
      have Hpos := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H
      rw [hd] at Hpos
      exact pos_of_mul_pos_right Hpos hc.le
    have hf : Measurable (fun z : Disorder (n+2) μ.maxDegree × ℝ => ψ z.1 u) :=
      hp.comp measurable_fst
    rw [(mixedMaximumPalmKernel_probability_and_formula n μ h hnp hL hm u hu).2 _ _ hf,
      hd,ENNReal.ofReal_mul hc.le]
    unfold maximumPalmExpectation
    rw [←mul_assoc, mul_assoc (ENNReal.ofReal (mathfrakC n μ Q)),
      ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hZ) ENNReal.ofReal_ne_top,mul_one,
      ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro k
    rw [ENNReal.ofReal_mul hc.le,mul_assoc]
    simp only [c,T,mul_assoc]
  · simp only [dite_eq_right hu]

/- The standard no-atom fact is proved by finite-variable polynomial
slicing, rather than retained as a literature interface. -/
private theorem mvPolynomial_ne_zero_ae_fin (d : ℕ) (ν : Fin d → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] [∀ i, NullSingletonClass (ν i)]
    (P : MvPolynomial (Fin d) ℝ) (hP : P ≠ 0) :
    ∀ᵐ x ∂Measure.pi ν, MvPolynomial.eval x P ≠ 0 := by
  induction d with
  | zero =>
    have hC : ∃ r : ℝ, MvPolynomial.C r = P :=
      (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).symm.surjective P
    obtain ⟨r, rfl⟩ := hC
    have hr : r ≠ 0 := by intro hr; exact hP (by simp [hr])
    exact .of_forall fun x => by simpa using hr
  | succ d ih =>
    let R := MvPolynomial.finSuccEquiv ℝ d P
    have hR : R ≠ 0 := by
      intro hz
      exact hP ((MvPolynomial.finSuccEquiv ℝ d).injective (hz.trans (map_zero _).symm))
    have hcoeff : R.coeff R.natDegree ≠ 0 := by
      simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hR
    have htail := ih (fun i => ν i.succ) (R.coeff R.natDegree) hcoeff
    have hm : MeasurableSet {z : ℝ × (Fin d → ℝ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) P ≠ 0} := by
      have hc : Continuous (fun z : ℝ × (Fin d → ℝ) => (Fin.cons z.1 z.2 : Fin (d+1) → ℝ)) := by
        fun_prop
      exact (isClosed_eq ((MvPolynomial.continuous_eval P).comp hc)
        continuous_const).measurableSet.compl
    have hslice : ∀ᵐ y ∂Measure.pi (fun i => ν i.succ),
        ∀ᵐ t ∂ν 0, MvPolynomial.eval (Fin.cons t y) P ≠ 0 := by
      filter_upwards [htail] with y hy
      have hpoly : R.map (MvPolynomial.eval y) ≠ 0 := by
        intro hz
        have hc := congrArg (fun q : ℝ[X] => q.coeff R.natDegree) hz
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy hc
      have hz := (Polynomial.finite_setOfPred_isRoot hpoly).countable.ae_notMem (ν 0)
      simpa only [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.IsRoot, mem_ofPred_eq, R] using hz
    have hprod := (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hslice)
    have hpull := (measurePreserving_piFinSuccAbove ν 0).quasiMeasurePreserving.ae hprod
    filter_upwards [hpull] with x hx
    have heq : Fin.cons
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0) x).1
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0) x).2 = x := by
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
        Fin.consEquiv, Equiv.coe_fn_mk, Function.uncurry_apply_pair] using
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm_apply_apply x
    rwa [heq] at hx

/-- The same polynomial null-set theorem in any finite coordinate system. -/
private theorem mvPolynomial_ne_zero_ae {ι : Type} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NullSingletonClass (ν i)]
    (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    ∀ᵐ x ∂Measure.pi ν, MvPolynomial.eval x P ≠ 0 := by
  let e := (Fintype.equivFin ι).symm
  let P' := MvPolynomial.renameEquiv ℝ e.symm P
  have hP' : P' ≠ 0 := by
    intro hz
    exact hP ((MvPolynomial.renameEquiv ℝ e.symm).injective
      (hz.trans (map_zero _).symm))
  have h := mvPolynomial_ne_zero_ae_fin _ (fun i => ν (e i)) P' hP'
  have mp := measurePreserving_piCongrLeft ν e
  rw [← mp.map_eq]
  apply (ae_map_iff mp.measurable.aemeasurable
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet.compl).mpr
  convert h using 1
  ext x
  simp only [mem_ofPred_eq, P', MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  have he : (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) x = x ∘ e.symm := by
    ext i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
  rw [he]


/-- The characteristic determinant as a polynomial in independent upper
entries, before pushing them forward to the symmetric matrix. -/
private def upperDeterminantPolynomial (d : ℕ) (k : ℝ) : MvPolynomial (UpperIndex d) ℝ :=
  Matrix.det (fun i j : Fin d =>
    (if h : i ≤ j then (MvPolynomial.X (⟨(i,j),h⟩ : UpperIndex d) : MvPolynomial (UpperIndex d) ℝ) else
      MvPolynomial.X ⟨(j,i),le_of_lt (lt_of_not_ge h)⟩) -
    if i = j then MvPolynomial.C k else 0)

/-- Evaluation recovers the literal shifted GOE matrix determinant. -/
private theorem upperDeterminantPolynomial_eval (d : ℕ) (k : ℝ) (x : UpperIndex d → ℝ) :
    MvPolynomial.eval x (upperDeterminantPolynomial d k) =
      (symmetricMatrix x - k • 1).det := by
  rw [upperDeterminantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_sub]
  simp [symmetricMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    apply_ite (MvPolynomial.eval x)]
  split_ifs <;> simp

/-- The determinant polynomial is nonzero: evaluating at `(k+1) I`
gives the identity determinant, equal to one. -/
private theorem upperDeterminantPolynomial_ne_zero (d : ℕ) (k : ℝ) :
    upperDeterminantPolynomial d k ≠ 0 := by
  let x : UpperIndex d → ℝ := fun ij => if ij.1.1 = ij.1.2 then k+1 else 0
  have hmat : symmetricMatrix x - k • 1 = 1 := by
    ext i j
    simp only [symmetricMatrix, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, x]
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := Ne.symm hij
      split_ifs <;> simp_all
  intro hz
  have he := upperDeterminantPolynomial_eval d k x
  rw [hz, map_zero, hmat, Matrix.det_one] at he
  exact zero_ne_one he

/-- Every fixed shift gives a nonsingular GOE matrix almost surely.
Only positivity of the variances and the independent upper coordinates
are used; no eigenvalue-density theorem enters. -/
theorem goe_shifted_det_ne_zero_ae (d N : ℕ) (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) (k : ℝ) :
    ∀ᵐ W ∂SphericalGaussianJet.goeLaw d N b, (W - k • 1).det ≠ 0 := by
  let v : UpperIndex d → ℝ≥0 := fun ij =>
    ((b / (N : ℝ)) * (if ij.1.1 = ij.1.2 then 2 else 1)).toNNReal
  have hv (ij : UpperIndex d) : v ij ≠ 0 := by
    apply ne_of_gt
    apply Real.toNNReal_pos.mpr
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    split_ifs <;> positivity
  let (ij : UpperIndex d) : NullSingletonClass (gaussianReal 0 (v ij)) :=
    nullSingletonClass_gaussianReal (hv ij)
  have h := mvPolynomial_ne_zero_ae (fun ij => gaussianReal 0 (v ij))
    (upperDeterminantPolynomial d k) (upperDeterminantPolynomial_ne_zero d k)
  unfold SphericalGaussianJet.goeLaw
  have hm : Measurable (fun W : Matrix (Fin d) (Fin d) ℝ => (W-k • 1).det) := by
    fun_prop
  apply (ae_map_iff (symmetricMatrix_measurable d).aemeasurable
    ((measurableSet_singleton 0).preimage hm).compl).mpr
  filter_upwards [h] with x hx
  simpa only [mem_compl_iff, mem_preimage, mem_singleton_iff,
    ← upperDeterminantPolynomial_eval] using hx

/-- A symmetric matrix with a fixed top eigenvalue has zero shifted
determinant, including all finite dimensions in the source convention. -/
private theorem det_eq_zero_of_top_eigenvalue_eq (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hW : ∀ i j, W i j = W j i) (k : ℝ) (hk : eigenvalues n W 0 = k) :
    (W-k • 1).det = 0 := by
  have hp : (k • 1-W).det = ∏ i, (k-eigenvalues n W i) := by
    simpa only [eigenvalues, gaussianToMatrix_matrixToGaussian] using
      shifted_det_eq_prod k (matrixToGaussian W) hW
  have hz : (k • 1-W).det = 0 := by
    rw [hp]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by rw [hk, sub_self])
  have he : W-k • 1 = -(k • 1-W) := by abel
  rw [he, Matrix.det_neg, hz, mul_zero]

/-- The source's GOE no-fixed-top-eigenvalue interface is a theorem. -/
theorem goeNoFixedTopEigenvalue : GOENoFixedTopEigenvalue := by
  intro n N hN b hb k
  filter_upwards [goe_shifted_det_ne_zero_ae (n+1) N hN hb k,
    SphericalMarkedWindows.goe_symmetric_ae (n+1) N b] with W hdet hsym
  intro hk
  exact hdet (det_eq_zero_of_top_eigenvalue_eq n W hsym k hk)

/-- The moving-cutoff determinant mean has its ordinary adjugate
derivative without any literature hypothesis. -/
theorem maximumMean_hasDerivAt (n N : ℕ) (hN : 0 < N) {b : ℝ}
    (hb : 0 < b) (k : ℝ) :
    HasDerivAt (maximumMean n N b) (maximumAdjugateMean n N b k) k :=
  SourcePureDeterminantDerivative.maximumMean_hasDerivAt goeNoFixedTopEigenvalue n N hN hb k

/-- Manuscript `prop:mo-pure` (b): the physical maximum intensity's
uniform `C/N` logarithmic slope estimate, with the GOE interface discharged. -/
theorem pureLocalMaxPhysicalIntensity_log_slope_rate
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp a ha
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ,
      (p : ℝ)*H/(n+2 : ℕ) ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z →
      |deriv (fun t => Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q t).toReal) H-
        deriv (pureMarkedComplexity p hp a ha Q) (H/(n+2 : ℕ))| ≤ C/(n+2 : ℕ) :=
  SourcePureDeterminantDerivative.pureLocalMaxPhysicalIntensity_log_slope_rate
    goeNoFixedTopEigenvalue p hp a ha hQ hg

/-- The same interface-free slope bound for the literal radial truncation
on the Euler graph, throughout its open support. -/
theorem pureGraphMaximumIntensity_log_slope_rate
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    (U : Set ℝ) (hU : IsOpen U) {g Z : ℝ} (hg : 0 < g)
    (hgap : U ⊆ Icc (2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g) Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ, (p : ℝ)*H/(n+2 : ℕ) ∈ U →
      |deriv (fun t => Real.log (pureGraphMaximumIntensity n p hp a ha Q U t).toReal) H-
        deriv (pureMarkedComplexity p hp a ha Q) (H/(n+2 : ℕ))| ≤ C/(n+2 : ℕ) :=
  SourcePureDeterminantDerivative.pureGraphMaximumIntensity_log_slope_rate
    goeNoFixedTopEigenvalue p hp a ha hQ U hU hg hgap

/-- The printed scalar physical prefactor `A_{N,p}`, expressed using the
already identified sphere area and zero-gradient density. -/
def purePhysicalA (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  (sphereKRPrefactor (n+1) μ Q).toReal / Real.sqrt (2*Real.pi*(n+2:ℕ)*μ.xi Q)

/-- The scalar Gaussian factor has exactly the manuscript's physical
normalization, including the raw-energy Jacobian. -/
theorem purePhysicalCoefficient_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (H : ℝ) :
    purePhysicalCoefficient n μ Q H = ENNReal.ofReal
      (purePhysicalA n μ Q*Real.exp (-H^2/(2*(n+2:ℕ)*μ.xi Q))) := by
  let N : ℝ := (n+2:ℕ)
  let T : ℝ := 2*Real.pi*μ.xi Q
  have hN : 0 < N := by dsimp [N]; positivity
  have hT : 0 < T := by dsimp [T]; exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (μ.xi_pos hQ)
  have hs : Real.sqrt (N/T)*Real.sqrt (T*N)=N := by
    apply (sq_eq_sq₀ (by positivity : 0 ≤ Real.sqrt (N/T)*Real.sqrt (T*N)) hN.le).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    field_simp
  have hcoef : N⁻¹*Real.sqrt (N/T)=(Real.sqrt (T*N))⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (Real.sqrt_pos.mpr (mul_pos hT hN)).ne').mp
    rw [mul_assoc,hs,inv_mul_cancel₀ hN.ne']
  have hGauss : -(n+2:ℕ)*(H/(n+2:ℕ))^2/(2*μ.xi Q) =
      -H^2/(2*(n+2:ℕ)*μ.xi Q) := by field_simp
  rw [purePhysicalCoefficient,physicalValuePdf,hGauss,
    ←ENNReal.ofReal_toReal (sphereKRPrefactor_ne_top (n+1) μ Q),
    ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  congr 1
  have hTN : 2*Real.pi*(n+2:ℕ)*μ.xi Q=T*N := by dsimp [T,N]; ring
  unfold purePhysicalA
  rw [hTN]
  change _ = (sphereKRPrefactor (n+1) μ Q).toReal / Real.sqrt (T*N)*_
  calc
    _ = (sphereKRPrefactor (n+1) μ Q).toReal * (N⁻¹*Real.sqrt (N/T)) *
        Real.exp (-H^2/(2*(n+2:ℕ)*μ.xi Q)) := by ring
    _ = _ := by rw [hcoef]; ring

/-- The exterior scalar Palm law is a genuine probability kernel on its
natural energy domain, not only a family of probability measures. -/
theorem pureMaximumPalmKernel_markov_on_exterior (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    IsMarkovKernel ((pureMaximumPalmKernel n p hp a ha Q u hu).comap
      (fun e : {e : ℝ // 0 < (p:ℝ)*e} => e.1) measurable_subtype_coe) := by
  constructor
  intro e
  exact (pureMaximumPalmKernel_eq_and_probability n p hp a ha hQ u hu e.1 e.2).2

private theorem weighted_count_mono {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {K K' : Set (EuclideanSpace ℝ (Fin 2))} (hKK' : K ⊆ K')
    (ψ ψ' : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (hψ : ∀ J u, ψ J u ≤ ψ' J u) (J : Disorder (n+1) P) :
    actualScoreWindowCount n c K ψ J ≤ actualScoreWindowCount n c K' ψ' J := by
  rw [actualScoreWindowCount_eq_indicator,actualScoreWindowCount_eq_indicator]
  unfold SphericalKacRiceGluing.actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro u
  by_cases hu : actualScore c J u ∈ K
  · simp only [ite_eq_left hu,ite_eq_left (hKK' hu)]
    exact hψ J u
  · simp only [ite_eq_right hu,zero_le]

private theorem retained_mean_mono (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {K K' : Set (EuclideanSpace ℝ (Fin 2))} (hKK' : K ⊆ K')
    (κ C ε η E G : ℝ) :
    sourceRetainedScoreWindowMean (n+1) μ Q K κ C ε η E G ≤
      sourceRetainedScoreWindowMean (n+1) μ Q K' κ C ε η E G := by
  unfold sourceRetainedScoreWindowMean
  have hfinite := bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ K'
    (fun _ _ => 1) 1 (by simp) (by simp)
  have htop := (lintegral_mono (sourceRetainedScoreWindowCount_le_unfiltered (n+1)
    (centerCoefficients (mixtureCoefficients μ) Q) K' κ C ε η E G)).trans_lt hfinite
  apply ENNReal.toReal_mono htop.ne
  exact lintegral_mono (weighted_count_mono (n+1) _ hKK' _ _ (fun _ _ => le_rfl))

private theorem retained_mean_le_maximum_tail (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (H : ℝ) (U : Set ℝ)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : K ⊆ physicalEnergyWindow (n+2) (Ici H) U)
    {κ : ℝ} (hκ : 0 < κ) (C ε η E G : ℝ) :
    sourceRetainedScoreWindowMean (n+1) μ Q K κ C ε η E G ≤
      (sourceMaximumTailCountMass n μ Q H U).toReal := by
  unfold sourceRetainedScoreWindowMean
  rw [sourceMaximumTailCountMass_def]
  have hfinite := sourceMaximumTailCountMass_finite n μ hQ H U
  rw [sourceMaximumTailCountMass_def] at hfinite
  apply ENNReal.toReal_mono hfinite.ne
  apply lintegral_mono_ae
  filter_upwards [actualLocalMaxCount_eq_negative_ae (n+1) (by omega) μ hQ
    (physicalEnergyWindow (n+2) (Ici H) U)] with J hJ
  rw [hJ,actualNegativeCriticalCount_eq_mark,sourceRetainedScoreWindowCount_eq_selected_maxima (n+1) _ K hκ]
  apply weighted_count_mono (n+1) _ hK
  intro A u
  exact mul_le_of_le_one_right zero_le (sourceSelectionMark_le_one _ κ C ε η E G A u)

private theorem tail_from_strict_windows (b t : ℝ) (hb : 0 < b)
    (A B : ℕ → ℝ) (W : ℝ → ℕ → ℝ)
    (hB : Tendsto B atTop (𝓝 (Real.exp (-b*t))))
    (hW : ∀ R : ℝ, t < R → Tendsto (W R) atTop (𝓝 (Real.exp (-b*t)-Real.exp (-b*R))))
    (hbound : ∀ n R, t < R → W R n ≤ A n ∧ A n ≤ B n) :
    Tendsto A atTop (𝓝 (Real.exp (-b*t))) := by
  have hdecay : Tendsto (fun R : ℝ => Real.exp (-b*R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  apply tendsto_order.2
  constructor
  · intro r hr
    obtain ⟨R,hR,hsmall⟩ := ((eventually_gt_atTop t).and
      (hdecay.eventually (gt_mem_nhds (sub_pos.mpr hr)))).exists
    filter_upwards [(hW R hR).eventually
      (eventually_gt_nhds (by linarith : r < Real.exp (-b*t)-Real.exp (-b*R)))] with n hn
    exact hn.trans_le (hbound n R hR).1
  · intro r hr
    filter_upwards [hB.eventually (gt_mem_nhds hr)] with n hn
    exact (hbound n (t+1) (by linarith)).2.trans_lt hn

private theorem mixed_retained_limits_of_filter (μ : FiniteMixture)
    {β x Q κ C ε η L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (hκ : 0 < κ)
    (hAd : Admissible μ β x Q L R δ) (hF : MixedFilterOn μ β x Q κ C ε η L R δ)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) :
    (∀ a b : ℝ, a < b → Tendsto (fun n : ℕ => sourceRetainedPhysicalWindowMean n μ Q
      (Ioo L R) (d.center n+a) (d.center n+b) κ C ε η (markE μ β x Q)
        (gap μ Q (markY β Q) (markZ x Q) ε η))
          atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b)))) ∧
    (∀ t : ℝ, Tendsto (fun n : ℕ => retainedTailMean n μ Q (Ioo L R) d.center δ κ C ε η
      (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η) t)
        atTop (𝓝 (Real.exp (-(β*x)*t)))) := by
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hδ := hAd.width
  have hEdge := hAd.edge
  have hL := hAd.contact.1
  have hR := hAd.contact.2
  obtain ⟨c,A,B,hc,_hA,_hB,hpost⟩ := hF
  let error := fun n : ℕ => B*Real.exp (-(c/2)*(n+2:ℕ))
  have herror : Tendsto error atTop (𝓝 0) := by
    have H := (source_dimension_exp_tail_tendsto 2 (half_pos hc)).const_mul B
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [] with n
    congr 2
    ring
  have hwindow : ∀ a b : ℝ, a < b → Tendsto (fun n : ℕ => sourceRetainedPhysicalWindowMean n μ Q
      (Ioo L R) (d.center n+a) (d.center n+b) κ C ε η E G)
        atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) := by
    intro a b hab
    have hall := d.critical_window_limit a b hab
    have hlo : Tendsto (fun n : ℕ => (1-error n)*
        sourceCriticalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b)) atTop
          (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) := by
      have hOne : Tendsto (fun _n : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [sub_zero,one_mul] using (hOne.sub herror).mul hall
    have hbound : ∀ᶠ n : ℕ in atTop,
        (1-error n)*sourceCriticalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b) ≤
          sourceRetainedPhysicalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b) κ C ε η E G ∧
        sourceRetainedPhysicalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b) κ C ε η E G ≤
          sourceCriticalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b) := by
      filter_upwards [hpost,herror.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
        source_logarithmic_center_offset_bounds (mul_pos h.beta_pos h.weight_range.1)
          d.log_constant_pos.le hδ d.center d.logarithmic_correction a b] with n hn herr hcenter
      let K := physicalEnergyWindow (n+2) (Icc (d.center n+a) (d.center n+b)) (Ioo L R)
      have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _
        (measurableSet_Icc.preimage (measurable_const_mul ((n+2:ℕ):ℝ))) measurableSet_Ioo
      have hW : ∀ (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)), ∀ z ∈ K,
          let cQ := centerCoefficients (mixtureCoefficients μ) Q
          let ν := mixedConditionedLaw cQ u hu z
          ENNReal.ofReal (1-error n)*(∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤
            ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*sourceSelectionMark cQ κ C ε η E G J u ∂ν := by
        intro u hu z hz
        have hmarks := source_physical_window_subset_coarse hcenter.1 hcenter.2 hz
        have hzR : z 1 ∈ Icc L R := ⟨hmarks.2.1,hmarks.2.2⟩
        have H := (hn u hu (z 0) hmarks.1 (z 1) hzR).2.2
        have heq : scorePairEquiv (z 0,z 1)=z := by
          apply PiLp.ext
          intro i
          fin_cases i <;> rfl
        simpa only [heq] using H
      have H := source_mixed_retained_window_mean_bounds (n+1) (by omega) μ h.overlap_range.1 hnp K hK
        κ C ε η E G (error n) herr.le hW
      simpa only [K,sourceUnfilteredScoreWindowMean_physical,sourceRetainedPhysicalWindowMean] using H
    exact hlo.squeeze' hall (hbound.mono fun _ hn => hn.1) (hbound.mono fun _ hn => hn.2)
  refine ⟨hwindow,?_⟩
  intro t
  let box := rectangularScoreWindow (Icc (E-δ) (E+δ)) univ
  let A := fun n : ℕ => retainedTailMean n μ Q (Ioo L R) d.center δ κ C ε η E G t
  let B := fun n : ℕ => (sourceMaximumTailCountMass n μ Q (d.center n+t) (Ioo L R)).toReal
  let W := fun b : ℝ => fun n : ℕ => sourceRetainedScoreWindowMean (n+1) μ Q
    (physicalEnergyWindow (n+2) (Icc (d.center n+t) (d.center n+b)) (Ioo L R) ∩ box)
      κ C ε η E G
  have hB : Tendsto B atTop (𝓝 (Real.exp (-(β*x)*t))) :=
    (d.tail_limit t).congr' ((sourceMaximumTailCountMass_toReal_eq μ h hnp hEdge ⟨hL,hR⟩).mono
      (fun n hn => (hn (d.center n+t)).symm))
  have hW : ∀ b : ℝ, t < b → Tendsto (W b) atTop (𝓝 (Real.exp (-(β*x)*t)-Real.exp (-(β*x)*b))) := by
    intro b htb
    apply (hwindow t b htb).congr'
    filter_upwards [source_logarithmic_center_offset_bounds (mul_pos h.beta_pos h.weight_range.1)
      d.log_constant_pos.le hδ d.center d.logarithmic_correction t b] with n hn
    have hsub : physicalEnergyWindow (n+2) (Icc (d.center n+t) (d.center n+b)) (Ioo L R) ⊆ box := by
      intro z hz
      have H := source_physical_window_subset_coarse hn.1 hn.2 hz
      exact ⟨H.1,mem_univ _⟩
    dsimp [W,sourceRetainedPhysicalWindowMean]
    rw [inter_eq_left.mpr hsub]
  apply tail_from_strict_windows (β*x) t (mul_pos h.beta_pos h.weight_range.1) A B W hB hW
  intro n b _htb
  constructor
  · apply retained_mean_mono n μ h.overlap_range.1
    intro z hz
    exact ⟨⟨hz.1.1.1,hz.1.2⟩,hz.2⟩
  · exact retained_mean_le_maximum_tail n μ h.overlap_range.1 (d.center n+t) (Ioo L R)
      inter_subset_left hκ C ε η E G

/-- Fixed retained windows and the genuinely unbounded retained upper tail
on a specified actual unit-tail center. -/
def MixedRetainedLimitsOn (μ : FiniteMixture) (β x Q κ C ε η L R δ : ℝ)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) : Prop :=
  (∀ a b : ℝ, a < b → Tendsto (fun n : ℕ => sourceRetainedPhysicalWindowMean n μ Q
    (Ioo L R) (d.center n+a) (d.center n+b) κ C ε η (markE μ β x Q)
      (gap μ Q (markY β Q) (markZ x Q) ε η))
        atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b)))) ∧
  (∀ t : ℝ, Tendsto (fun n : ℕ => retainedTailMean n μ Q (Ioo L R) d.center δ κ C ε η
    (markE μ β x Q) (gap μ Q (markY β Q) (markZ x Q) ε η) t)
      atTop (𝓝 (Real.exp (-(β*x)*t))))

/-- The mixed one-point interface on one literal admissible witness,
including retained-intensity ratios and both retained count limits on the
same actual normalized center. All probabilistic inputs are proved internally. -/
theorem mixed_onePoint_filter_count_common_witness (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : sourceRadialEdge μ Q < L₀) (hm : markK μ β Q ∈ Ioo L₀ R₀) :
    let κ := (L₀-sourceRadialEdge μ Q)/4
    ∃ C : ℝ, 0 < κ ∧ 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        ∃ L R δ : ℝ, L₀ < L ∧ R < R₀ ∧
          δ < gap μ Q (markY β Q) (markZ x Q) ε η/4 ∧
          Admissible μ β x Q L R δ ∧ AllHighOn μ β x Q κ C L R δ ∧
          MixedFilterOn μ β x Q κ C ε η L R δ ∧
          MixedRetainedRatioOn μ β x Q κ C ε η L R δ ∧
          SourceMarkedRadialConclusions μ β x Q L R δ ∧
          ∃ d : SourceMaximumAllConclusions μ β x Q L R δ,
            MixedRetainedLimitsOn μ β x Q κ C ε η L R δ d.first_moments := by
  obtain ⟨C,hκ,hC,hη,hηone,hcommon⟩ := mixed_onePoint_common_witness_with_ratio μ h hnp hEdge hm
  refine ⟨C,hκ,hC,hη,hηone,?_⟩
  intro ε hε hεη
  obtain ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,hRatio,hRad,⟨d⟩⟩ := hcommon ε hε hεη
  exact ⟨L,R,δ,hL,hR,hδG,hA,hHigh,hF,hRatio,hRad,d,
    mixed_retained_limits_of_filter μ h hnp hκ hA hF d.first_moments⟩

/-- The same selection event, rate and constants remain valid on every
smaller closed mark rectangle. Only the literal admissibility of a later
consumer needs to be checked again. -/
theorem MixedFilterOn.shrink_box {μ : FiniteMixture} {β x Q κ C ε η L R δ L' R' δ' : ℝ}
    (hF : MixedFilterOn μ β x Q κ C ε η L R δ)
    (hL : L ≤ L') (hR : R' ≤ R) (hδ : δ' ≤ δ) :
    MixedFilterOn μ β x Q κ C ε η L' R' δ' := by
  obtain ⟨c,A,B,hc,hA,hB,hpost⟩ := hF
  refine ⟨c,A,B,hc,hA,hB,?_⟩
  filter_upwards [hpost] with n hn
  intro u hu e he k hk
  have hb := filter_box_shrinking hL hR hδ he hk
  exact hn u hu e hb.1 k hb.2

/-- The all-critical scalar intensity with exactly the same open radial
truncation as the maximum graph intensity. -/
def pureGraphCriticalIntensity (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q : ℝ) (U : Set ℝ) (H : ℝ) : ℝ≥0∞ :=
  if (p:ℝ)*H/(n+2:ℕ) ∈ U then pureCriticalPhysicalIntensity n p hp a ha Q H else 0

/-- One actual pure normalized center, with both species of expected counts
and the physical density limit at every fixed energy shift. -/
structure PureScalarNormalization (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (β x Q l r : ℝ) where
  center : ℕ → ℝ
  cutoff : ℕ
  log_constant : ℝ
  log_constant_pos : 0 < log_constant
  fallback : ∀ n < cutoff, center n=(n+2:ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q
  normalization : ∀ n ≥ cutoff,
    ExpectedTailCentering.tail (pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2:ℕ)*l) ((n+2:ℕ)*r)) (center n)=1 ∧
    (∀ y : ℝ, ExpectedTailCentering.tail (pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2:ℕ)*l) ((n+2:ℕ)*r)) y=1 → y=center n) ∧
    |center n-((n+2:ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
      Real.log (n+2:ℕ)/(2*(β*x)))| ≤ log_constant
  density_limit : ∀ t : ℝ, Tendsto (fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2:ℕ)*l) ((n+2:ℕ)*r) (center n+t)) atTop (𝓝 ((β*x)*Real.exp (-(β*x)*t)))
  maximum_tail : ∀ t : ℝ, Tendsto (fun n : ℕ => ExpectedTailCentering.tail
    (pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r)) (center n+t))
      atTop (𝓝 (Real.exp (-(β*x)*t)))
  critical_tail : ∀ t : ℝ, Tendsto (fun n : ℕ => ExpectedTailCentering.tail
    (sourcePureTruncatedCriticalDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r)) (center n+t))
      atTop (𝓝 (Real.exp (-(β*x)*t)))
  maximum_window : ∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
    sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (center n+L) (center n+R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))
  critical_window : ∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
    sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r (center n+L) (center n+R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))

/-- The pure contact identities, global complexity loss, literal truncated
density bounds, and actual maximum-density slope on one radial interval. -/
structure PureScalarEstimates (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (β x Q l r : ℝ) : Prop where
  contact_zero : pureMarkedComplexity p hp a ha Q (markE (FiniteMixture.pure p hp a ha) β x Q)=0
  contact_slope : HasDerivAt (pureMarkedComplexity p hp a ha Q) (-(β*x))
    (markE (FiniteMixture.pure p hp a ha) β x Q)
  quadratic_loss : ∀ e : ℝ, pureMarkedComplexity p hp a ha Q e ≤
    -(β*x)*(e-markE (FiniteMixture.pure p hp a ha) β x Q)-
      ((p:ℝ)-2)/(4*((p:ℝ)-1)*(FiniteMixture.pure p hp a ha).xi Q)*
        (e-markE (FiniteMixture.pure p hp a ha) β x Q)^2
  density_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ e : ℝ, (p:ℝ)*e ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r) →
      ENNReal.ofReal (c*(Real.sqrt (n+2:ℕ))⁻¹*Real.exp ((n+2:ℕ)*pureMarkedComplexity p hp a ha Q e)) ≤
        pureGraphMaximumIntensity n p hp a ha Q (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) ((n+2:ℕ)*e) ∧
      pureGraphMaximumIntensity n p hp a ha Q (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) ((n+2:ℕ)*e) ≤
        pureGraphCriticalIntensity n p hp a ha Q (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) ((n+2:ℕ)*e) ∧
      pureGraphCriticalIntensity n p hp a ha Q (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) ((n+2:ℕ)*e) ≤
        ENNReal.ofReal (C*(Real.sqrt (n+2:ℕ))⁻¹*Real.exp ((n+2:ℕ)*pureMarkedComplexity p hp a ha Q e))
  log_slope : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ,
    (p:ℝ)*H/(n+2:ℕ) ∈ Ioo ((p:ℝ)*l) ((p:ℝ)*r) →
      |deriv (fun t => Real.log (pureGraphMaximumIntensity n p hp a ha Q
        (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) t).toReal) H-
          deriv (pureMarkedComplexity p hp a ha Q) (H/(n+2:ℕ))| ≤ C/(n+2:ℕ)

/-- The scalar analytic/count part of `prop:mo-pure` on one arbitrary
exterior graph interval and one exact unit-tail center. The GOE no-atom
hypothesis has been discharged, and all amplitudes and parities are allowed.
The localization/filter clauses of part (d) are not asserted here. -/
theorem pure_scalar_onePoint_common (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q l r g Z : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p:ℝ)*l)
    (hRight : (p:ℝ)*r ≤ Z) :
    PureScalarEstimates p hp a ha β x Q l r ∧
      Nonempty (PureScalarNormalization p hp a ha β x Q l r) ∧
      ∀ n : ℕ, ∀ H : ℝ,
        (pureGraphMaximumIntensity n p hp a ha Q (Ioo ((p:ℝ)*l) ((p:ℝ)*r)) H).toReal =
          pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r) H := by
  let μ := FiniteMixture.pure p hp a ha
  have hgap : Ioo ((p:ℝ)*l) ((p:ℝ)*r) ⊆ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z := by
    intro k hk
    exact ⟨hLeft.trans hk.1.le,hk.2.le.trans hRight⟩
  obtain ⟨hz,hd,hquad⟩ := pure_complexity_contact_and_quadratic p hp a ha h
  have hEst : PureScalarEstimates p hp a ha β x Q l r := by
    refine ⟨hz,hd,hquad,?_,pureGraphMaximumIntensity_log_slope_rate p hp a ha
      h.overlap_range.1 _ isOpen_Ioo hg hgap⟩
    obtain ⟨c,C,hc,hC,hbounds⟩ := pure_localMax_physical_prefactors p hp a ha h.overlap_range.1 (Z:=Z) hg
    refine ⟨c,C,hc,hC,?_⟩
    filter_upwards [hbounds] with n hn
    intro e he
    have heq : (p:ℝ)*((n+2:ℕ)*e)/(n+2:ℕ)=(p:ℝ)*e := by field_simp
    simp only [pureGraphMaximumIntensity,pureGraphCriticalIntensity,heq,ite_eq_left he]
    exact hn e (hgap he)
  obtain ⟨n₀,m,M,hM,hfallback,hcenter,hdensity,htail,hctail,hwindow,hcwindow⟩ :=
    pure_onePoint_normalized_limits p hp a ha h hm hg hLeft hRight
  have hlog : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2:ℕ)*markE μ β x Q-Real.log (n+2:ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (hcenter n hn).2.2
  have hdensityShift (t : ℝ) : Tendsto (fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2:ℕ)*l) ((n+2:ℕ)*r) (m n+t)) atTop (𝓝 ((β*x)*Real.exp (-(β*x)*t))) := by
    have hratio := sourcePure_truncatedLocalMax_centered_ratio p hp a ha h hm m hM hlog t
    have hpos := hdensity.eventually (eventually_gt_nhds (mul_pos h.beta_pos h.weight_range.1))
    have H := hratio.mul hdensity
    have H' : Tendsto (fun n : ℕ =>
        (pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r) (m n+t) /
          pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r) (m n)) *
          pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2:ℕ)*l) ((n+2:ℕ)*r) (m n))
        atTop (𝓝 ((β*x)*Real.exp (-(β*x)*t))) := by
      simpa only [mul_comm] using H
    apply H'.congr'
    filter_upwards [hpos] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  let d : PureScalarNormalization p hp a ha β x Q l r := {
    center := m
    cutoff := n₀
    log_constant := M
    log_constant_pos := hM
    fallback := hfallback
    normalization := hcenter
    density_limit := hdensityShift
    maximum_tail := htail
    critical_tail := hctail
    maximum_window := hwindow
    critical_window := hcwindow }
  exact ⟨hEst,⟨d⟩,fun n H => pureGraphMaximumIntensity_eq_truncated n p hp a ha Q l r H⟩

/-- Proper-pure posterior selection and determinant retention, with the
full-sphere regularity premise discharged and the exact collar chosen before
ε. This uses value/zero-gradient conditioning and never inverts the singular
mixed score covariance. -/
theorem pure_filter_and_retained_weight (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-sourceRadialEdge μ Q)/2
    ∃ C : ℝ, 0 < C ∧
      let η := 1-Real.cos (min (Real.pi/4) ((g/2)/(2*C)))
      0 < η ∧ η < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1-η →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ δ cp Ap cw Aw : ℝ, 0 < δ ∧ δ < G/4 ∧ 0 < cp ∧ 0 < Ap ∧ 0 < cw ∧ 0 < Aw ∧
          ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
            ∀ e ∈ Icc (E-δ) (E+δ),
              let c := centerCoefficients (mixtureCoefficients μ) Q
              let ν := valueConditionedLaw c u hu e
              ν.real {J | ¬sourceSelectionEvent c (g/2) C ε η E G J u} ≤ Ap*Real.exp (-cp*(n+2:ℕ)) ∧
              ENNReal.ofReal (1-Aw*Real.exp (-cw*(n+2:ℕ)))*
                (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤
                  ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*sourceSelectionMark c (g/2) C ε η E G J u ∂ν := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-sourceRadialEdge μ Q)/2
  have hg : 0 < g := div_pos (sub_pos.mpr (sourceContact_markK_above_edge μ h)) (by norm_num)
  let M := |E|+2
  obtain ⟨C,hC,hreg⟩ := source_value_physical_posterior_sphere_regularity μ h.overlap_range.1
    (show 0 ≤ M by dsimp [M]; positivity)
  let η := 1-Real.cos (min (Real.pi/4) ((g/2)/(2*C)))
  have hθ : 0 < min (Real.pi/4) ((g/2)/(2*C)) := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ : min (Real.pi/4) ((g/2)/(2*C)) < Real.pi/2 :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (min (Real.pi/4) ((g/2)/(2*C))) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθπ⟩
  have hcos1 : Real.cos (min (Real.pi/4) ((g/2)/(2*C))) < 1 := by
    have H := Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=min (Real.pi/4) ((g/2)/(2*C)))
      (by norm_num) (by linarith [Real.pi_pos]) hθ
    simpa only [Real.cos_zero] using H
  have hη : 0 < η := sub_pos.mpr hcos1
  refine ⟨C,hC,hη,by linarith,?_⟩
  intro ε hε hεη
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hG : 0 < G := (pure_source_trial_gap p hp a ha h hε hη hεη).1
  have hMBound : |E|+1+1 ≤ M := by dsimp [M]; linarith
  obtain ⟨δp,hδp,hδpG,_hδpOne,gp,_hgp,hprob⟩ :=
    source_pure_physical_posterior_selection_failure_fixed_regularity p hp a ha h hε hη hεη
      (by norm_num : (0:ℝ)<1) hC hMBound hreg
  obtain ⟨δw,C₂,hδw,_hδwG,_hδwOne,hC₂,gw,_hgw,_herror,hweight⟩ :=
    source_pure_physical_posterior_determinant_selection_loss_fixed_regularity p hp a ha h hε hη hεη
      (by norm_num : (0:ℝ)<1) hC hMBound hreg
  obtain ⟨cp,Ap,hcp,hAp,hprate⟩ := failure_rate_exponential μ h.overlap_range.1 hG hg gp
  obtain ⟨Aw,cw,hAw,hcw,hwrate⟩ := sourceSelectionWeightError_exponential C₂ hC₂ μ h.overlap_range.1 hG hg gw
  let δ := min δp δw
  have hδ : 0 < δ := lt_min hδp hδw
  refine ⟨δ,cp,Ap,cw,Aw,hδ,(min_le_left _ _).trans_lt hδpG,hcp,hAp,hcw,hAw,?_⟩
  filter_upwards [hprob,hweight] with n hn hw
  intro u hu e he
  have hep : e ∈ Icc (E-δp) (E+δp) := by
    have hh := min_le_left δp δw
    constructor <;> linarith [he.1,he.2]
  have hew : e ∈ Icc (E-δw) (E+δw) := by
    have hh := min_le_right δp δw
    constructor <;> linarith [he.1,he.2]
  refine ⟨(hn u hu e hep).trans (hprate n),?_⟩
  apply le_trans _ (hw.2 u hu e hew)
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.ofReal_le_ofReal
  change 1-Aw*Real.exp (-cw*(n+2:ℕ)) ≤ 1-sourceSelectionWeightError C₂ μ Q G g gw n
  linarith [hwrate n]

/-- Every smaller exterior interval containing the contact admits a
positive energy width with all four literal admissibility conditions. -/
theorem Admissible.narrow_radial {μ : FiniteMixture} {β x Q L R δ L' R' : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hA : Admissible μ β x Q L R δ) (hL : L ≤ L') (hR : R' ≤ R)
    (hm : markK μ β Q ∈ Ioo L' R') :
    ∃ δ' : ℝ, δ' ≤ δ ∧ Admissible μ β x Q L' R' δ' := by
  obtain ⟨a,ha,hclear⟩ :=
    SphericalTAPMixedSaddleClearanceChoice.sourceRadialSaddle_nearby_half_clearance μ h hnp hm
  let d := sourceMarkedLeastCurvature μ Q*
    (sourceRadialClearance μ β Q (Ioo L' R'))^2/(8*(β*x))
  have hd : 0 < d := by
    have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
      (by have := h.min_degree; omega) hnp
    have hu := sourceRadialClearance_pos μ hm
    have hc := mul_pos h.beta_pos h.weight_range.1
    dsimp [d]
    positivity
  let δ' := min δ (min d a)
  have hδ' : 0 < δ' := lt_min hA.width (lt_min hd ha)
  have hδδ : δ' ≤ δ := min_le_left _ _
  have hδd : δ' ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ' ≤ a := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ',hδδ,hA.edge.trans_le hL,hm,hδ',?_,hδd,?_⟩
  · intro e he k hk
    apply hA.score e ⟨by linarith [he.1],by linarith [he.2]⟩ k
    exact ⟨hL.trans hk.1,hk.2.trans hR⟩
  · intro e he
    exact hclear e ⟨by linarith [he.1],by linarith [he.2]⟩

end SlowEquilibration.SourceMixedOnePointComplete
