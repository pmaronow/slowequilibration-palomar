-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerProof
public import SlowEquilibration.PressureLowerTails
public import SlowEquilibration.GaussianSpinLogConvex

/-!
The three analytic statements in the lower band argument are recorded with
their finite-dimensional normalizations. The assembly below uses the actual
untruncated zero-overlap replicated pressure, including the correction from
transverse dimension to ambient dimension.

The Gaussian projection inequality proves that the replicated Taylor linear
term can be removed in expectation on every finite positive compact spin
restriction. This is a partial reduction: neither the required pressure
lower tails nor the full expected thick-latitude comparison is asserted.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerComplete

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof LiteratureSubagBandLowerProof
open SourceLiteratureParisi
open SphericalTaylorRemainder SphericalGaussianJet WholeFieldRegression
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Uniform-frame output needed for the sequential slab argument. The
positive exponent may depend on the slab width and tolerance: unlike the
unnormalized pressure lower tail, this includes a full-partition denominator. -/
def UniformSlabLowerTails (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ j : ℕ, ∀ ρ t : ℝ, 0 < ρ → 0 < t → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop,
      uniformSlabLowerTailProbability N j μ β ρ t ≤ Real.exp (-c * (N : ℝ))

/-- The zero-overlap replicated pressure without a logarithmic floor, at
the transverse temperature and normalized per ambient dimension. -/
def residualReplicatedPressure (μ : FiniteMixture) (β q ρ : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1) (k n : ℕ) : ℝ :=
  ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) *
    expectedReplicatedBandPressure k (physicalResidualMixture μ q hq)
      (β * Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ))) 0 1 ρ (0 : Vector n)

/-- The residual pressure limit retains every fixed positive replica count
and every positive overlap tolerance. -/
def ResidualReplicatedLimit {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : Prop :=
  ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ →
    ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n => residualReplicatedPressure μ β q ρ hq k n)
        atTop (𝓝 (D.residual q))

/-- Expected thick-latitude comparison, with a transverse tolerance chosen
before dimension. The Taylor linear term is included in this comparison. -/
def ExpectedThickLatitudeLowerComparison (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1, ∀ δ ρ : ℝ, 0 < δ → 0 < ρ →
    ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ n : ℕ in atTop,
        Real.log (1 - q) / 2 + residualReplicatedPressure μ β q θ hq k n - ε ≤
          expectedReplicatedBandPressure k μ β q δ ρ (canonicalBandCenter n q)

/-- The two analytic pressure statements imply the original lower
approximation, with no change to its quantifiers or tolerances. -/
theorem expectedBandLowerApproximation_of_residual_and_thickLatitude
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hresidual : ResidualReplicatedLimit D)
    (hthick : ExpectedThickLatitudeLowerComparison μ β) :
    ExpectedBandLowerApproximation D := by
  apply (expectedBandLowerApproximation_iff_canonicalFixedParameters D).mpr
  intro q hq ε hε δ ρ hδ hρ k hk
  obtain ⟨θ, hθ, hcomp⟩ := hthick q hq δ ρ hδ hρ k hk (ε / 2) (by positivity)
  have hlim := hresidual q hq θ hθ k hk
  have hnear := hlim.eventually (lt_mem_nhds (show D.residual q - ε / 2 <
    D.residual q by linarith))
  filter_upwards [hcomp, hnear] with n hc hn
  linarith

private theorem finite_logPartition_lipschitz {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V)
    [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (GaussianSpinInterpolation.logPartition ν L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).differentiable
      (by norm_num))
  intro w
  rw [(GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
  apply (NNReal.coe_le_coe).mp
  change ‖GaussianSpinInterpolation.score ν L w‖ ≤ (K.toNNReal : ℝ)
  rw [Real.coe_toNNReal K hK]
  exact GaussianSpinInterpolation.norm_score_le ν L hL hK hb w

private theorem finite_logPartition_linear_integrable {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V)
    [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    Integrable (fun w => GaussianSpinInterpolation.logPartition ν L (T w))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let f := GaussianSpinInterpolation.logPartition ν L
  have hf := finite_logPartition_lipschitz ν L hL hK hb
  have hbound (w : EuclideanSpace ℝ ι) :
      ‖f (T w)‖ ≤ K * ‖T‖ * ‖w‖ + ‖f 0‖ := by
    have h := hf.norm_sub_le (T w) 0
    rw [Real.coe_toNNReal K hK, sub_zero] at h
    calc
      _ ≤ ‖f (T w) - f 0‖ + ‖f 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f (T w) - f 0) (f 0)
      _ ≤ K * ‖T w‖ + ‖f 0‖ := add_le_add h le_rfl
      _ ≤ K * (‖T‖ * ‖w‖) + ‖f 0‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (T.le_opNorm w) hK) le_rfl
      _ = _ := by ring
  apply (((IsGaussian.integrable_id
    (μ := stdGaussian (EuclideanSpace ℝ ι))).norm.const_mul (K * ‖T‖)).add
      (integrable_const ‖f 0‖)).mono'
    (hf.continuous.comp T.continuous).aestronglyMeasurable
  exact .of_forall hbound

/-- Removing any orthogonal Gaussian coefficient component can only
decrease the expected log partition. The spin measure may be a restricted
replica block and is only required to have finite positive mass. -/
theorem expected_logPartition_starProjection_le {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (S : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (∫ w, GaussianSpinInterpolation.logPartition ν L (S.starProjection w)
      ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      ∫ w, GaussianSpinInterpolation.logPartition ν L w
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let f := GaussianSpinInterpolation.logPartition ν L
  have hf := finite_logPartition_lipschitz ν L hL hK hb
  have hconv : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, ?_⟩
    intro w _ v _ a b ha hb' hab
    have h := (GaussianSpinInterpolation.logPartition_line_convex ν L hL hK hb
      w (v - w)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb' hab
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul,
      add_zero, one_smul, add_sub_cancel] at h
    have heq : w + b • (v - w) = a • w + b • v := by
      have he : b = 1 - a := by linarith
      rw [he]
      module
    rw [heq] at h
    exact h
  have hpoint (w : EuclideanSpace ℝ ι) :
      f (S.starProjection w) ≤ (1 / 2 : ℝ) * f w + (1 / 2 : ℝ) * f (S.reflection w) := by
    have h := hconv.2 (mem_univ w) (mem_univ (S.reflection w))
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (by norm_num)
    have heq : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • S.reflection w =
        S.starProjection w := by
      rw [Submodule.reflection_apply]
      module
    simpa only [heq, smul_eq_mul] using h
  have hproj := finite_logPartition_linear_integrable ν L hL hK hb S.starProjection
  have hid : Integrable f (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [ContinuousLinearMap.id_apply] using
      finite_logPartition_linear_integrable ν L hL hK hb
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι))
  have hrefl := finite_logPartition_linear_integrable ν L hL hK hb
    S.reflection.toContinuousLinearEquiv.toContinuousLinearMap
  have hmp : MeasurePreserving S.reflection
      (stdGaussian (EuclideanSpace ℝ ι)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨S.reflection.continuous.measurable, stdGaussian_map S.reflection⟩
  have he := hmp.integral_comp S.reflection.toHomeomorph.measurableEmbedding f
  have h := integral_mono hproj
    ((hid.const_mul (1 / 2 : ℝ)).add (hrefl.const_mul (1 / 2 : ℝ))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hid.const_mul (1 / 2 : ℝ)) (hrefl.const_mul (1 / 2 : ℝ)),
    integral_const_mul, integral_const_mul] at h
  change (∫ w, f (S.starProjection w) ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
    (1 / 2 : ℝ) * (∫ w, f w ∂stdGaussian (EuclideanSpace ℝ ι)) +
      (1 / 2 : ℝ) * (∫ w, f (S.reflection w) ∂stdGaussian (EuclideanSpace ℝ ι)) at h
  rw [he] at h
  linarith

/-- The expected linear-perturbation inequality for bounded Gaussian
features with orthogonal coefficient banks. It applies to a restricted
replica spin measure without introducing independent replacement disorder. -/
theorem expected_logPartition_le_add_orthogonal {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (R D : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hR : Measurable R) (hD : Measurable D)
    {KR KD : ℝ} (hKR : 0 ≤ KR) (hKD : 0 ≤ KD)
    (hbR : ∀ᵐ v ∂ν, ‖R v‖ ≤ KR) (hbD : ∀ᵐ v ∂ν, ‖D v‖ ≤ KD)
    (horth : ∀ v w, D v ((R w).adjoint 1) = 0) :
    (∫ g, GaussianSpinInterpolation.logPartition ν R g
      ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      ∫ g, GaussianSpinInterpolation.logPartition ν (fun v => R v + D v) g
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let S : Submodule ℝ (EuclideanSpace ℝ ι) := ⨅ v, (D v).ker
  have hrow (v : V) : (R v).adjoint 1 ∈ S :=
    (Submodule.mem_iInf _).mpr (fun w => horth w v)
  have hDzero (v : V) (g : EuclideanSpace ℝ ι) : D v (S.starProjection g) = 0 :=
    (Submodule.mem_iInf _).mp (S.starProjection_apply_mem g) v
  have hRproj (v : V) (g : EuclideanSpace ℝ ι) :
      R v (S.starProjection g) = R v g := by
    have hadj (x : EuclideanSpace ℝ ι) :
        inner ℝ x ((R v).adjoint 1) = R v x := by
      rw [(R v).adjoint_inner_right]
      simp
    calc
      _ = inner ℝ (S.starProjection g) ((R v).adjoint 1) := (hadj _).symm
      _ = inner ℝ g (S.starProjection ((R v).adjoint 1)) :=
        S.starProjection_isSymmetric g ((R v).adjoint 1)
      _ = inner ℝ g ((R v).adjoint 1) :=
        congrArg (fun x => inner ℝ g x) (Submodule.starProjection_eq_self_iff.mpr (hrow v))
      _ = _ := hadj g
  have hb : ∀ᵐ v ∂ν, ‖R v + D v‖ ≤ KR + KD := by
    filter_upwards [hbR, hbD] with v hvR hvD
    exact (norm_add_le _ _).trans (add_le_add hvR hvD)
  have heq (g : EuclideanSpace ℝ ι) :
      GaussianSpinInterpolation.logPartition ν (fun v => R v + D v)
        (S.starProjection g) = GaussianSpinInterpolation.logPartition ν R g := by
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
      GaussianSpinInterpolation.weight
    congr 1
    apply integral_congr_ae
    exact .of_forall fun v => by simp only [_root_.add_apply, hRproj, hDzero,
      add_zero]
  simpa only [heq] using expected_logPartition_starProjection_le ν
    (fun v => R v + D v) (hR.add hD) (add_nonneg hKR hKD) hb S

private theorem scalarFeature_continuous {V ι : Type*} [TopologicalSpace V]
    [Fintype ι] [DecidableEq ι]
    (F : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hF : ∀ g, Continuous (fun v => F v g)) : Continuous F := by
  let b := EuclideanSpace.basisFun ι ℝ
  have heq : F = fun v => ∑ i : ι, F v (b i) • EuclideanSpace.proj i := by
    funext v
    ext g
    simp only [_root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, EuclideanSpace.coe_proj]
    calc
      F v g = F v (∑ i, g i • b i) := congrArg (F v) (b.sum_repr g).symm
      _ = _ := by simp [map_sum, map_smul, mul_comm]
  rw [heq]
  exact continuous_finsetSum _ (fun i _ => (hF (b i)).smul continuous_const)

/-- The Taylor linear term cannot lower the disorder-expected replicated
log partition. The measure may be any finite positive restriction of a
compact transverse replica space. This uses the original tensor disorder. -/
theorem expected_replicatedTaylor_logPartition_le
    {V : Type*} [TopologicalSpace V] [CompactSpace V]
    [MeasurableSpace V] [BorelSpace V] {N P k : ℕ} (hN : 0 < N)
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (m : Vector N)
    (z : Fin k → V → Vector N) (hz : ∀ i, Continuous (z i))
    (ht : ∀ i v, inner ℝ (z i v) m = 0) :
    (∫ J : Disorder N P, Real.log (∫ v,
      Real.exp (β * ∑ i : Fin k,
        taylorRemainderCLM c m (z i v) (euclideanDisorder J)) ∂ν)
      ∂disorderLaw N P) ≤
      ∫ J : Disorder N P, Real.log (∫ v,
        Real.exp (β * ∑ i : Fin k,
          (field c J (m + z i v) - field c J m)) ∂ν)
        ∂disorderLaw N P := by
  classical
  let R : V → EuclideanDisorder N P →L[ℝ] ℝ :=
    fun v => β • ∑ i : Fin k, taylorRemainderCLM c m (z i v)
  let D : V → EuclideanDisorder N P →L[ℝ] ℝ :=
    fun v => β • ∑ i : Fin k, directionObservation c m (z i v)
  have hR : Continuous R := by
    apply scalarFeature_continuous
    intro g
    simp only [R, _root_.smul_apply, _root_.sum_apply,
      smul_eq_mul]
    exact (continuous_finsetSum _ (fun i _ =>
      taylorRemainder_parameter_continuous c m (z i) (hz i) g)).const_mul β
  have hD : Continuous D := by
    apply scalarFeature_continuous
    intro g
    simp only [D, _root_.smul_apply, _root_.sum_apply,
      smul_eq_mul, directionObservation, flatJetCLM_apply, jet, iteratedFDeriv_one_apply]
    exact (continuous_finsetSum _ (fun i _ =>
      (fderiv ℝ (field c (unpackDisorder g)) m).continuous.comp (hz i))).const_mul β
  obtain ⟨KR, hKR⟩ := isCompact_univ.exists_bound_of_continuousOn hR.continuousOn
  obtain ⟨KD, hKD⟩ := isCompact_univ.exists_bound_of_continuousOn hD.continuousOn
  have hbR : ∀ᵐ v ∂ν, ‖R v‖ ≤ max KR 0 :=
    .of_forall fun v => (hKR v (mem_univ v)).trans (le_max_left _ _)
  have hbD : ∀ᵐ v ∂ν, ‖D v‖ ≤ max KD 0 :=
    .of_forall fun v => (hKD v (mem_univ v)).trans (le_max_left _ _)
  have hcross (v w : V) : D v ((R w).adjoint 1) = 0 := by
    simp only [D, _root_.smul_apply, _root_.sum_apply,
      smul_eq_mul]
    have hzero (i : Fin k) : directionObservation c m (z i v) ((R w).adjoint 1) = 0 := by
      rw [scalar_coupling_comm]
      simp only [R, _root_.smul_apply, _root_.sum_apply,
        smul_eq_mul, taylorRemainder_direction_orthogonal hN c hc m _ _ (ht _ _),
        Finset.sum_const_zero, mul_zero]
    simp only [hzero, Finset.sum_const_zero, mul_zero]
  have hineq := expected_logPartition_le_add_orthogonal ν R D hR.measurable hD.measurable
    (le_max_right _ _) (le_max_right _ _) hbR hbD hcross
  have hsum : ∀ᵐ v ∂ν, ‖R v + D v‖ ≤ max KR 0 + max KD 0 := by
    filter_upwards [hbR, hbD] with v hvR hvD
    exact (norm_add_le _ _).trans (add_le_add hvR hvD)
  have hleft := (actual_flattened_gaussian N P).integral_comp
    (finite_logPartition_lipschitz ν R hR.measurable (le_max_right _ _) hbR).continuous.aestronglyMeasurable
  have hright := (actual_flattened_gaussian N P).integral_comp
    (finite_logPartition_lipschitz ν (fun v => R v + D v) (hR.add hD).measurable
      (add_nonneg (le_max_right _ _) (le_max_right _ _)) hsum).continuous.aestronglyMeasurable
  rw [← hleft, ← hright] at hineq
  convert hineq using 1
  · congr 1
    funext J
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
      GaussianSpinInterpolation.weight
    simp only [R, _root_.smul_apply, _root_.sum_apply,
      smul_eq_mul, one_mul, Function.comp_def]
  · congr 1
    funext J
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
      GaussianSpinInterpolation.weight
    congr 1
    apply integral_congr_ae
    exact .of_forall fun v => by
      simp only [R, D, _root_.add_apply, _root_.smul_apply,
        _root_.sum_apply, smul_eq_mul, one_mul, taylorRemainderCLM_actual,
        directionObservation_actual, ← Finset.sum_add_distrib, ← mul_add]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      ring

end SlowEquilibration.LiteratureSubagBandLowerComplete
