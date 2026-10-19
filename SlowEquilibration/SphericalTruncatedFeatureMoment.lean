-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.TruncatedGramSplit
public import SlowEquilibration.SphericalHSCentralSecondMoment
public import SlowEquilibration.SphericalTemperatureStability
public import SlowEquilibration.SphericalCentralOverlapPerturbation

@[expose] public section

/-! True truncated disorder-feature barycenters and their weighted
Huang--Sellke second moments. Every quantity uses the actual finite tensor
feature and the genuine sphere/disorder probability laws. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unnormalized truncated gradient feature, without differentiating
the disorder-dependent truncation indicator. -/
def truncatedFeatureMean {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (T : Set (Disorder N P×Vector N)) (J : Disorder N P) : EuclideanDisorder N P :=
  ∫x,T.indicator (fun z => Real.exp (β*field c z.1 z.2) • (β • fieldFeature c z.2)) (J,x) ∂sphereLaw N

theorem truncatedFeatureMean_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    {T : Set (Disorder N P×Vector N)} (hT : MeasurableSet T) :
    Measurable (truncatedFeatureMean c β T) := by
  have hf : StronglyMeasurable (T.indicator (fun z : Disorder N P×Vector N =>
      Real.exp (β*field c z.1 z.2) • (β • fieldFeature c z.2))) := by
    apply StronglyMeasurable.indicator _ hT
    apply Continuous.stronglyMeasurable
    exact ((Real.continuous_exp.comp ((field_jointContinuous c).const_mul β)).smul
      ((fieldFeature_continuous c).comp continuous_snd |>.const_smul β))
  exact hf.integral_prod_right'.measurable

/-- Actual central weighted two-spin partition, with N retained. -/
def weightedOverlapPairPartition {N P : ℕ} (c : Degree P → ℝ) (β δ : ℝ)
    (J : Disorder N P) : ℝ :=
  ∫p : Vector N×Vector N,(smallOverlap δ).indicator
    (fun z => (N:ℝ)*|covariancePolynomial c (overlap z.1 z.2)| * 
      Real.exp (β*field c J z.1)*Real.exp (β*field c J z.2)) p
        ∂(sphereLaw N).prod (sphereLaw N)

def weightedCentralOverlapMoment {P : ℕ} (N : ℕ) (c : Degree P → ℝ) (β δ : ℝ) : ℝ :=
  ∫p : Vector N×Vector N,(smallOverlap δ).indicator
    (fun z => (N:ℝ)*|covariancePolynomial c (overlap z.1 z.2)| * 
      Real.exp ((N:ℝ)*β^2*covariancePolynomial c (overlap z.1 z.2))) p
        ∂(sphereLaw N).prod (sphereLaw N)

/-- The genuine finite-volume vector HS estimate. -/
theorem hsTruncatedFeatureMean_sq_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β)
    (δ L : ℝ) (J : Disorder N P) :
    ‖truncatedFeatureMean c β (hsTruncation c β δ L) J‖^2 ≤
      β^2*weightedOverlapPairPartition c β δ J+
        β^2*(N:ℝ)*covariancePolynomial c 1*Real.exp L*partition N β (field c J) := by
  let A := fun x : Vector N => β • fieldFeature c x
  let W := fun x : Vector N => Real.exp (β*field c J x)
  let U : Set (Vector N) := {x | (J,x)∈hsTruncation c β δ L}
  let M := β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)
  have hA : Measurable A := ((fieldFeature_continuous c).const_smul β).measurable
  have hbound : ∀ᵐx ∂sphereLaw N,‖A x‖ ≤ M := by
    filter_upwards [sphereLaw_support hN] with x hx
    dsimp [A,M]
    rw [norm_smul,Real.norm_of_nonneg hβ,fieldFeature_norm hN c hc x hx]
  have hM : 0 ≤ M := mul_nonneg hβ (Real.sqrt_nonneg _)
  have hU : MeasurableSet U := (hsTruncation_measurable c β δ L).preimage
    (measurable_const.prodMk measurable_id)
  have hWi : Integrable W (sphereLaw N) := partition_integrand_integrable hN β (field_contDiff c J).continuous
  have hfar : ∀ᵐu ∂sphereLaw N,u∈U →
      (∫v,(smallOverlap δ)ᶜ.indicator (fun p : Vector N×Vector N => W p.2) (u,v) ∂sphereLaw N) ≤ Real.exp L :=
    .of_forall fun u hu => hu
  have hh := TruncatedGramSplit.feature_mean_sq_le (sphereLaw N) A hA hM hbound
    W (Real.continuous_exp.comp ((field_contDiff c J).continuous.const_mul β)).measurable hWi (fun _ => (Real.exp_pos _).le)
    U hU (smallOverlap δ) (smallOverlap_measurable δ) (Real.exp_pos L).le hfar
  have hMean : (∫x,U.indicator (fun y => W y • A y) x ∂sphereLaw N)=
      truncatedFeatureMean c β (hsTruncation c β δ L) J := by
    unfold truncatedFeatureMean
    apply integral_congr_ae
    exact .of_forall fun x => by
      by_cases hx : (J,x)∈hsTruncation c β δ L <;> simp [U,W,A,hx]
  have hGram : (∫p : Vector N×Vector N,(smallOverlap δ).indicator
      (fun z => |inner ℝ (A z.1) (A z.2)| * W z.1*W z.2) p ∂(sphereLaw N).prod (sphereLaw N))=
      β^2*weightedOverlapPairPartition c β δ J := by
    rw [weightedOverlapPairPartition,← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun p => by
      by_cases hp : p∈smallOverlap δ
      · simp only [Set.indicator_of_mem hp,A,W,real_inner_smul_left,real_inner_smul_right,
          fieldFeature_inner_gram hN c hc]
        rw [abs_mul,abs_of_nonneg hβ,abs_mul,abs_of_nonneg hβ,abs_mul,
          abs_of_nonneg (Nat.cast_nonneg N)]
        ring
      · simp [hp]
  have hc1 : 0 ≤ covariancePolynomial c 1 := by
    unfold covariancePolynomial
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hc p) (by positivity)
  have hMsq : M^2=β^2*(N:ℝ)*covariancePolynomial c 1 := by
    dsimp [M]
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hc1)]
    ring
  rw [hMean,hGram,hMsq] at hh
  exact hh

/-- The actual weighted pair integrand is integrable under the literal three
probability laws, needed for the ensuing Fubini exchange. -/
theorem weighted_overlap_pair_prod_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) (β δ : ℝ) :
    Integrable (fun z : Disorder N P×(Vector N×Vector N) =>
      (smallOverlap δ).indicator (fun p => (N:ℝ)*|covariancePolynomial c (overlap p.1 p.2)| * 
        Real.exp (β*field c z.1 p.1)*Real.exp (β*field c z.1 p.2)) z.2)
      ((disorderLaw N P).prod ((sphereLaw N).prod (sphereLaw N))) := by
  have hi := field_exp_pair_prod_integrable hN c hc β
  apply (hi.const_mul ((N:ℝ)*covariancePolynomial c 1)).mono'
  · have hcont : Continuous (fun z : Disorder N P×(Vector N×Vector N) =>
        (N:ℝ)*|covariancePolynomial c (overlap z.2.1 z.2.2)| * 
          Real.exp (β*field c z.1 z.2.1)*Real.exp (β*field c z.1 z.2.2)) := by
      have hk : Continuous (fun z : Disorder N P×(Vector N×Vector N) =>
          (N:ℝ)*|covariancePolynomial c (overlap z.2.1 z.2.2)|) := by
        unfold covariancePolynomial overlap
        fun_prop
      exact (hk.mul (Real.continuous_exp.comp (((field_jointContinuous c).comp
        (continuous_fst.prodMk continuous_snd.fst)).const_mul β))).mul
          (Real.continuous_exp.comp (((field_jointContinuous c).comp
            (continuous_fst.prodMk continuous_snd.snd)).const_mul β))
    exact hcont.aestronglyMeasurable.indicator
      ((smallOverlap_measurable δ).preimage measurable_snd)
  · have hp : ∀ᵐz : Disorder N P×(Vector N×Vector N)
        ∂(disorderLaw N P).prod ((sphereLaw N).prod (sphereLaw N)),
        ‖z.2.1‖^2=(N:ℝ) ∧ ‖z.2.2‖^2=(N:ℝ) := by
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_eq_fun (measurable_snd.fst.norm.pow_const 2) measurable_const).inter
          (measurableSet_eq_fun (measurable_snd.snd.norm.pow_const 2) measurable_const))).mpr
      exact .of_forall fun _ => sphereLaw_pair_support hN
    filter_upwards [hp] with z hz
    have hb := abs_covariancePolynomial_le_at_one c hc
      (abs_le.mpr (overlap_mem_Icc_of_norm_sq hN z.2.1 z.2.2 hz.1 hz.2))
    have hc1 : 0 ≤ covariancePolynomial c 1 := (abs_nonneg _).trans hb
    by_cases hs : z.2∈smallOverlap δ
    · rw [Set.indicator_of_mem hs,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N))
        (mul_nonneg (Real.exp_pos (β*field c z.1 z.2.1)).le (Real.exp_pos (β*field c z.1 z.2.2)).le)]
    · rw [Set.indicator_of_notMem hs,norm_zero]
      positivity

/-- Exact annealed normalization of the genuine weighted central pair term. -/
theorem expected_weightedOverlapPairPartition_eq {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) (β δ : ℝ) :
    (∫J,weightedOverlapPairPartition c β δ J ∂disorderLaw N P)=
      Real.exp (2*annealedExponent N c β)*weightedCentralOverlapMoment N c β δ := by
  have hi := weighted_overlap_pair_prod_integrable hN c hc β δ
  unfold weightedOverlapPairPartition weightedCentralOverlapMoment
  rw [integral_integral_swap hi,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sphereLaw_pair_support hN] with p hp
  by_cases hs : p∈smallOverlap δ
  · simp only [Set.indicator_of_mem hs]
    rw [show (fun J : Disorder N P => (N:ℝ)*|covariancePolynomial c (overlap p.1 p.2)| * 
      Real.exp (β*field c J p.1)*Real.exp (β*field c J p.2))=
      fun J => ((N:ℝ)*|covariancePolynomial c (overlap p.1 p.2)|)*
        (Real.exp (β*field c J p.1)*Real.exp (β*field c J p.2)) by funext J; ring,
      integral_const_mul]
    have hm := pair_truncated_exponential_moment hN c hc β p.1 p.2 hp.1 hp.2
      (T:=univ) MeasurableSet.univ
    simp only [Set.indicator_univ,Set.mem_univ,and_self,Set.ofPred_true,probReal_univ,mul_one] at hm
    rw [hm]
    have he : (N:ℝ)*β^2*(covariancePolynomial c 1+covariancePolynomial c (overlap p.1 p.2))=
        2*annealedExponent N c β+(N:ℝ)*β^2*covariancePolynomial c (overlap p.1 p.2) := by
      unfold annealedExponent
      ring
    rw [he,Real.exp_add]
    ring
  · simp only [Set.indicator_of_notMem hs,integral_zero,mul_zero]

end SlowEquilibration.SphericalModel
