-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalReversibility
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Actual mixed Langevin semigroup on Gibbs L²

The operators are lifted directly from the constructed measurable transition
kernels and their proved invariant Gibbs probability law. Square-integral
contraction, smooth-test symmetry and actual continuous paths provide the
Hilbert semigroup properties; no diagonal basis is supplied as a premise.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace ContDiff
namespace SlowEquilibration.SphericalL2Semigroup
open SphericalAging SphericalModel SphericalDynamics SphericalReversibility HardSphereDynamics
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace StationaryKernel
variable {E : Type*} [MeasurableSpace E]
  (π : Measure E) [IsProbabilityMeasure π] (K : Kernel E E) [IsMarkovKernel K]
  (hInv : K ∘ₘ π = π)

/-- Literal integration against a genuine stationary Markov kernel. -/
def average (f : E → ℝ) (x : E) : ℝ := ∫ y, f y ∂K x

omit [IsProbabilityMeasure π] [IsMarkovKernel K] in
lemma average_integrable {f : E → ℝ} (hf : Integrable f (K ∘ₘ π)) :
    Integrable (average K f) π := by
  rw [Measure.comp_eq_comp_const_apply] at hf
  exact hf.integral_comp

omit [IsProbabilityMeasure π] [IsMarkovKernel K] in
lemma integral_average {f : E → ℝ} (hf : Integrable f (K ∘ₘ π)) :
    (∫ x, average K f x ∂π) = ∫ y, f y ∂(K ∘ₘ π) := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  exact (Kernel.integral_comp hf).symm

include hInv

omit [IsProbabilityMeasure π] [IsMarkovKernel K] in
lemma ae_average_congr {f g : E → ℝ} (hfg : f =ᵐ[π] g) :
    average K f =ᵐ[π] average K g := by
  have h : f =ᵐ[K ∘ₘ π] g := by rw [hInv]; exact hfg
  exact (Measure.ae_ae_of_ae_comp h).mono (fun _ hx => integral_congr_ae hx)

omit [IsProbabilityMeasure π] in
/-- Jensen's square-integral bound for the literal representative,
with its conditional L² membership derived from stationary integration. -/
lemma average_square_le (U : Lp ℝ 2 π) :
    ∀ᵐ x ∂π, (average K U x) ^ 2 ≤ ∫ y, U y ^ 2 ∂K x := by
  have hi : Integrable (fun y => U y ^ 2) (K ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp U).integrable_sq
  have hslice := (Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi
  filter_upwards [hslice.1] with x hx
  have hm : MemLp (U : E → ℝ) 2 (K x) :=
    (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable U).aestronglyMeasurable).mpr hx
  have h := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq (K x) U hm
  simpa only [average, probReal_univ, one_mul] using h

omit [IsProbabilityMeasure π] in
/-- The literal kernel average belongs to actual Gibbs L². -/
lemma average_memLp (U : Lp ℝ 2 π) : MemLp (average K U) 2 π := by
  have hi : Integrable (fun y => U y ^ 2) (K ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp U).integrable_sq
  have hq : Integrable (fun x => ∫ y, U y ^ 2 ∂K x) π := average_integrable π K hi
  apply (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable U).integral_kernel.aestronglyMeasurable).mpr
  apply hq.mono' ((Lp.stronglyMeasurable U).integral_kernel.pow 2).aestronglyMeasurable
  filter_upwards [average_square_le π K hInv U] with x hx
  change ‖(average K U x) ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hx

/-- The genuine L² class obtained from the literal kernel representative. -/
def vector (U : Lp ℝ 2 π) : Lp ℝ 2 π := (average_memLp π K hInv U).toLp (average K U)

omit [IsProbabilityMeasure π] in
lemma vector_ae (U : Lp ℝ 2 π) : vector π K hInv U =ᵐ[π] average K U :=
  (average_memLp π K hInv U).coeFn_toLp

omit [IsProbabilityMeasure π] in
lemma vector_square_norm (U : Lp ℝ 2 π) :
    ‖vector π K hInv U‖ ^ 2 = ∫ x, (average K U x) ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vector_ae π K hInv U] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, ← pow_two]

omit [IsProbabilityMeasure π] in
/-- Actual square-integral contraction follows from literal Jensen and
stationarity, rather than from a norm estimate supplied as a premise. -/
lemma vector_norm_le (U : Lp ℝ 2 π) : ‖vector π K hInv U‖ ≤ ‖U‖ := by
  have hi : Integrable (fun y => U y ^ 2) (K ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp U).integrable_sq
  have hsq : ‖vector π K hInv U‖ ^ 2 ≤ ‖U‖ ^ 2 := by
    rw [vector_square_norm]
    calc
      _ ≤ ∫ x, ∫ y, U y ^ 2 ∂K x ∂π :=
        integral_mono_ae (average_memLp π K hInv U).integrable_sq
          (average_integrable π K hi) (average_square_le π K hInv U)
      _ = ∫ y, U y ^ 2 ∂π := by
        change (∫ x, average K (fun y => U y ^ 2) x ∂π) = _
        rw [integral_average π K hi, hInv]
      _ = ‖U‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        congr 1
        funext x
        simp [pow_two]
  nlinarith [norm_nonneg (vector π K hInv U), norm_nonneg U]

lemma vector_add (U V : Lp ℝ 2 π) :
    vector π K hInv (U + V) = vector π K hInv U + vector π K hInv V := by
  have hiU : Integrable (U : E → ℝ) (K ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp U).integrable (by norm_num)
  have hiV : Integrable (V : E → ℝ) (K ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp V).integrable (by norm_num)
  have hcoef := Measure.ae_ae_of_ae_comp (show (U + V : Lp ℝ 2 π) =ᵐ[K ∘ₘ π]
      (fun y => U y + V y) by rw [hInv]; exact Lp.coeFn_add U V)
  apply Lp.ext
  filter_upwards [vector_ae π K hInv (U + V), vector_ae π K hInv U,
    vector_ae π K hInv V, Lp.coeFn_add (vector π K hInv U) (vector π K hInv V),
    hcoef, (Measure.integrable_comp_iff hiU.aestronglyMeasurable).mp hiU |>.1,
    (Measure.integrable_comp_iff hiV.aestronglyMeasurable).mp hiV |>.1] with x hUV hU hV he hc hiU hiV
  rw [hUV, he]
  simp only [Pi.add_apply]
  rw [hU, hV]
  unfold average
  exact (integral_congr_ae hc).trans (integral_add hiU hiV)

omit [IsProbabilityMeasure π] in
lemma vector_smul (c : ℝ) (U : Lp ℝ 2 π) :
    vector π K hInv (c • U) = c • vector π K hInv U := by
  have hcoef := Measure.ae_ae_of_ae_comp (show (c • U : Lp ℝ 2 π) =ᵐ[K ∘ₘ π]
      (fun y => c • U y) by rw [hInv]; exact Lp.coeFn_smul c U)
  apply Lp.ext
  filter_upwards [vector_ae π K hInv (c • U), vector_ae π K hInv U,
    Lp.coeFn_smul c (vector π K hInv U), hcoef] with x hcU hU he hc
  rw [hcU, he]
  simp only [Pi.smul_apply]
  rw [hU]
  unfold average
  exact (integral_congr_ae hc).trans (integral_smul c (fun y => U y))

/-- The actual stationary-kernel operator, as a genuine Hilbert-space CLM. -/
def operator : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  LinearMap.mkContinuous
    { toFun := vector π K hInv
      map_add' := vector_add π K hInv
      map_smul' := vector_smul π K hInv }
    1 (fun U => by
      change ‖vector π K hInv U‖ ≤ 1 * ‖U‖
      rw [one_mul]
      exact vector_norm_le π K hInv U)

lemma operator_ae (U : Lp ℝ 2 π) : operator π K hInv U =ᵐ[π] average K U := by
  change vector π K hInv U =ᵐ[π] _
  exact vector_ae π K hInv U

lemma operator_norm_le : ‖operator π K hInv‖ ≤ 1 :=
  (operator π K hInv).opNorm_le_bound zero_le_one (fun U => by
    change ‖vector π K hInv U‖ ≤ 1 * ‖U‖
    rw [one_mul]
    exact vector_norm_le π K hInv U)

end StationaryKernel

variable {N : ℕ}

/-- The actual Gibbs Hilbert space for a realized finite mixed Hamiltonian. -/
abbrev Space (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :=
  Lp ℝ 2 (mixtureGibbsLaw μ β J)

/-- The actual mixed Langevin transition as a genuine operator on Gibbs L². -/
def P (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : Space μ J β →L[ℝ] Space μ J β := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact StationaryKernel.operator (mixtureGibbsLaw μ β J) (mixedTransitionKernel μ J β t)
    (mixedTransitionKernel_gibbs_invariant hN μ J β t)

theorem P_ae (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (U : Space μ J β) :
    P hN μ J β t U =ᵐ[mixtureGibbsLaw μ β J]
      fun x => ∫ y, U y ∂mixedTransitionKernel μ J β t x := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact StationaryKernel.operator_ae _ _ _ U

theorem P_norm_le (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : ‖P hN μ J β t‖ ≤ 1 := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact StationaryKernel.operator_norm_le _ _ _

theorem P_apply_norm_le (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (U : Space μ J β) : ‖P hN μ J β t U‖ ≤ ‖U‖ := by
  exact ((P hN μ J β t).le_opNorm U).trans
    ((mul_le_mul_of_nonneg_right (P_norm_le hN μ J β t) (norm_nonneg U)).trans_eq (one_mul _))

/-- At time zero, the actual Gibbs L² operator is the identity. -/
theorem P_zero (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) : P hN μ J β 0 = ContinuousLinearMap.id ℝ (Space μ J β) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Lp.ext
  filter_upwards [P_ae hN μ J β 0 U] with x hx
  rw [hx, mixedTransitionKernel_zero]
  exact integral_dirac U x

/-- The literal kernel Chapman–Kolmogorov identity descends to the
constructed actual Gibbs L² operators. -/
theorem P_add (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (s t : ℝ≥0) :
    P hN μ J β (s + t) = (P hN μ J β s).comp (P hN μ J β t) := by
  let π := mixtureGibbsLaw μ β J
  let := mixtureGibbsLaw_probability hN μ β J
  let K := mixedTransitionKernel μ J β
  have hInv (r) : K r ∘ₘ π = π := mixedTransitionKernel_gibbs_invariant hN μ J β r
  apply ContinuousLinearMap.ext
  intro U
  have hi : Integrable (U : State N → ℝ) (K (s + t) ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp U).integrable (by norm_num)
  have hslice := (Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi
  have hrepresent : (P hN μ J β t U : State N → ℝ) =ᵐ[K s ∘ₘ π]
      (fun x => ∫ y, U y ∂K t x) := by
    rw [hInv]
    exact P_ae hN μ J β t U
  have hpull := Measure.ae_ae_of_ae_comp hrepresent
  apply Lp.ext
  filter_upwards [P_ae hN μ J β (s + t) U,
    P_ae hN μ J β s (P hN μ J β t U), hslice.1, hpull] with x hst hs hi hx
  change (P hN μ J β (s + t) U) x = (P hN μ J β s (P hN μ J β t U)) x
  rw [hst, hs, mixedTransitionKernel_semigroup]
  change Integrable (U : State N → ℝ) (mixedTransitionKernel μ J β (s + t) x) at hi
  rw [mixedTransitionKernel_semigroup] at hi
  have hx' : (P hN μ J β t U : State N → ℝ) =ᵐ[mixedTransitionKernel μ J β s x]
      (fun z => ∫ y, U y ∂mixedTransitionKernel μ J β t z) := hx
  exact (Kernel.integral_comp hi).trans (integral_congr_ae hx'.symm)

/-- The actual operator maps any representative to the literal transition
expectation, modulo precisely the actual Gibbs null sets. -/
theorem P_ae_expectation (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (U : Space μ J β) {f : State N → ℝ}
    (hf : StronglyMeasurable f) (hUf : U =ᵐ[mixtureGibbsLaw μ β J] f) :
    P hN μ J β t U =ᵐ[mixtureGibbsLaw μ β J] mixedExpectation μ J β t f := by
  have hcongr := StationaryKernel.ae_average_congr (mixtureGibbsLaw μ β J)
    (mixedTransitionKernel μ J β t) (mixedTransitionKernel_gibbs_invariant hN μ J β t) hUf
  filter_upwards [P_ae hN μ J β t U, hcongr] with x hx hc
  exact hx.trans (hc.trans (mixedExpectation_eq_kernel μ J β t f hf x).symm)

/-- Genuine smooth compact test representatives form a dense subset of
this actual Gibbs Hilbert space. -/
def smoothCore (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) : Set (Space μ J β) :=
  {U | ∃ f : State N → ℝ, U =ᵐ[mixtureGibbsLaw μ β J] f ∧
    HasCompactSupport f ∧ ContDiff ℝ ∞ f}

theorem smoothCore_dense (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) : Dense (smoothCore μ J β) := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

/-- The literal compact C² transition balance is the actual Hilbert inner
product symmetry on the dense smooth core. -/
theorem P_smooth_inner (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (U V : Space μ J β)
    (hU : U ∈ smoothCore μ J β) (hV : V ∈ smoothCore μ J β) :
    inner ℝ (P hN μ J β t U) V = inner ℝ U (P hN μ J β t V) := by
  obtain ⟨f, hUf, hfc, hf⟩ := hU
  obtain ⟨g, hVg, hgc, hg⟩ := hV
  have hPU := P_ae_expectation hN μ J β t U hf.continuous.stronglyMeasurable hUf
  have hPV := P_ae_expectation hN μ J β t V hg.continuous.stronglyMeasurable hVg
  calc
    _ = ∫ x, mixedExpectation μ J β t f x * g x ∂mixtureGibbsLaw μ β J := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hPU, hVg] with x hpx hx
      simp [hpx, hx, RCLike.inner_apply, mul_comm]
    _ = ∫ x, f x * mixedExpectation μ J β t g x ∂mixtureGibbsLaw μ β J :=
      compact_mixedExpectation_reversible hN μ J β (hf.of_le (by simp)) hfc (hg.of_le (by simp)) hgc t
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hUf, hPV] with x hx hpx
      simp [hx, hpx, RCLike.inner_apply, mul_comm]

/-- Selfadjointness of the actual Gibbs L² transition follows by density
from the proved physical compact-test reversibility. -/
theorem P_isSymmetric (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : (P hN μ J β t).toLinearMap.IsSymmetric := by
  intro U V
  have hcore (A : Space μ J β) (hA : A ∈ smoothCore μ J β) (B : Space μ J β) :
      inner ℝ (P hN μ J β t A) B = inner ℝ A (P hN μ J β t B) := by
    exact (smoothCore_dense hN μ J β).induction
      (P := fun B => inner ℝ (P hN μ J β t A) B = inner ℝ A (P hN μ J β t B))
      (fun B hB => P_smooth_inner hN μ J β t A B hA hB)
      (isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner (P hN μ J β t).continuous)) B
  exact (smoothCore_dense hN μ J β).induction
    (P := fun A => inner ℝ (P hN μ J β t A) V = inner ℝ A (P hN μ J β t V))
    (fun A hA => hcore A hA V)
    (isClosed_eq ((P hN μ J β t).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) U

theorem P_isSelfAdjoint (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : IsSelfAdjoint (P hN μ J β t) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (P_isSymmetric hN μ J β t)

/-- The actual transitions are contractions also in Hilbert distance. -/
theorem P_dist_le (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (U V : Space μ J β) :
    dist (P hN μ J β t U) (P hN μ J β t V) ≤ dist U V := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact P_apply_norm_le hN μ J β t (U - V)

/-- Strong continuity on actual smooth compact observables follows from
the genuine transition continuity and bounded dominated convergence. -/
theorem P_smooth_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (U : Space μ J β) (hU : U ∈ smoothCore μ J β) :
    Continuous (fun t => P hN μ J β t U) := by
  let := mixtureGibbsLaw_probability hN μ β J
  obtain ⟨f, hUf, hfc, hf⟩ := hU
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hbound (t : ℝ≥0) (x : State N) : ‖mixedExpectation μ J β t f x‖ ≤ C := by
    rw [mixedExpectation_eq_actual]
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := VectorBrownian.law N)
        (f := fun omega => f (mixedProcess μ J β x t omega))
        (ae_of_all _ (fun omega => hC _)))
  have hjoint := (mixedExpectation_regular μ J β (hf.of_le (by simp)) hfc).2.1
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let E : ℝ≥0 → State N → ℝ := fun t x =>
    mixedExpectation μ J β t f x - mixedExpectation μ J β t₀ f x
  have hEm (t) : AEStronglyMeasurable (fun x => E t x ^ 2) (mixtureGibbsLaw μ β J) :=
    (((hjoint.comp (continuous_const.prodMk continuous_id)).sub
      (hjoint.comp (continuous_const.prodMk continuous_id))).pow 2).aestronglyMeasurable
  have hEb (t) (x) : ‖E t x ^ 2‖ ≤ (2 * C) ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have he : ‖E t x‖ ≤ 2 * C := (norm_sub_le _ _).trans
      ((add_le_add (hbound t x) (hbound t₀ x)).trans_eq (by ring))
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (E t x)) (mul_nonneg (by norm_num) hC0)).mpr he
  have hEt (x) : Tendsto (fun t => E t x ^ 2) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 => E t x ^ 2) :=
      ((hjoint.comp (continuous_id.prodMk continuous_const)).sub continuous_const).pow 2
    have ht : Tendsto (fun t => E t x ^ 2) (𝓝 t₀) (𝓝 (E t₀ x ^ 2)) := hc.continuousAt.tendsto
    simpa only [E, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht
  have hI : Tendsto (fun t => ∫ x, E t x ^ 2 ∂mixtureGibbsLaw μ β J) (𝓝 t₀) (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * C) ^ 2)
        (Eventually.of_forall hEm) (Eventually.of_forall (fun t => ae_of_all _ (hEb t)))
        (integrable_const _) (ae_of_all _ hEt))
  have hnorm (t : ℝ≥0) : ‖P hN μ J β t U - P hN μ J β t₀ U‖ ^ 2 =
      ∫ x, E t x ^ 2 ∂mixtureGibbsLaw μ β J := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [P_ae_expectation hN μ J β t U hf.continuous.stronglyMeasurable hUf,
      P_ae_expectation hN μ J β t₀ U hf.continuous.stronglyMeasurable hUf,
      Lp.coeFn_sub (P hN μ J β t U) (P hN μ J β t₀ U)] with x ht ht₀ hsub
    simp only [hsub, Pi.sub_apply, ht, ht₀, RCLike.inner_apply, conj_trivial, E, pow_two]
  have hsq : Tendsto (fun t => ‖P hN μ J β t U - P hN μ J β t₀ U‖ ^ 2)
      (𝓝 t₀) (𝓝 0) := hI.congr' (.of_forall (fun t => (hnorm t).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

/-- The genuine mixed Gibbs L² semigroup is strongly continuous on the
whole actual Hilbert space, derived from smooth density and contraction. -/
theorem P_apply_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (U : Space μ J β) : Continuous (fun t => P hN μ J β t U) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨V, hV, hUV⟩ := (smoothCore_dense hN μ J β).exists_dist_lt U
    (show 0 < ε / 3 by positivity)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    (P_smooth_continuous hN μ J β V hV).continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hmid := hclose ht
  have htriangle := dist_triangle (P hN μ J β t U) (P hN μ J β t V) (P hN μ J β t₀ U)
  have htriangle' := dist_triangle (P hN μ J β t V) (P hN μ J β t₀ V) (P hN μ J β t₀ U)
  have hleft := P_dist_le hN μ J β t U V
  have hright := P_dist_le hN μ J β t₀ V U
  rw [dist_comm V U] at hright
  linarith

end SlowEquilibration.SphericalL2Semigroup
