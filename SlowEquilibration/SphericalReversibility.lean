-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDynamics
public import SlowEquilibration.SphericalGibbs
public import SlowEquilibration.SphericalGeneratorFormula
public import SphericalAging.SphereSmoothTestMeasureExt
public import SphericalAging.L2ObservableJointC2
public import SphericalAging.FlowTerminalLpSpatialBounds
public import SphericalAging.FlowTerminalHessianContinuity
public import SphericalAging.FlowTerminalJointContinuity
public import SphericalAging.HamiltonianSecondCoefficientBounds
public import SphericalAging.LocalHorizonContinuity
public import SphericalAging.ActualC2Dynkin

@[expose] public section

/-!
# Actual mixed transition regularity, generator and reversibility

The statements below concern the literal mixed Langevin process and its
constructed measurable kernels. Analytic identities are derived from genuine
smooth stochastic flow and Itô providers, rather than supplied as hypotheses.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace ContDiff
namespace SlowEquilibration.SphericalReversibility
open SphericalAging HardSphereDynamics LocalSDE SphericalModel SphericalDynamics
open FlowTerminalDerivative C2ObservableDerivative CompactObservableGradient
open L2ObservableFamilyC2 L2ObservableJointC2 MultivariateTaylor
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

namespace Regularity
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
  {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (sigma i j))
  (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
  (hbd : ∀ i, LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j, LipschitzWith Ls (fderiv ℝ (sigma i j)))
  (hbd2 : ∀ i, LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀ i j, LipschitzWith Ms (fderiv ℝ (fderiv ℝ (sigma i j))))

/-- Literal clamped terminal state class of the actual smooth SDE. -/
def clampedState (T t : ℝ≥0) (x : State N) : Lp (State N) 2 P :=
  FlowTerminalDerivative.stateClass (NullAugmentation.driver D₀) hb hs x T (min t T)

def clampedExpectation (f : State N → ℝ) (T t : ℝ≥0) (x : State N) : ℝ :=
  observable f (clampedState D₀ hb hs T t x)

include hbg hsg hbd hsd in
lemma clampedState_fderiv (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) :
    fderiv ℝ (clampedState D₀ hb hs T t) = fun x =>
      stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T (min t T) :=
  funext (fun x => (stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd
    x T (min t T) hT).fderiv)

include hbg hsg hbd hsd hbd2 hsd2 in
/-- C² observable regularity comes from actual terminal stochastic flow
regularity and its actual fourth-moment increment bound. -/
theorem clampedExpectation_regular (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ≥0) (hT : 0 < T) :
    (∀ t, ContDiff ℝ 2 (clampedExpectation D₀ hb hs f T t)) ∧
    Continuous (fun q : ℝ≥0 × State N => clampedExpectation D₀ hb hs f T q.1 q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (clampedExpectation D₀ hb hs f T q.1) q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => Hessian (clampedExpectation D₀ hb hs f T q.1) q.2) := by
  let X := clampedState D₀ hb hs T
  have hX (t) : ContDiff ℝ 2 (X t) :=
    FlowTerminalSpatialC2.stateClass_contDiff_two D₀ hbg hsg hb hs hbd hsd hbd2 hsd2
      T hT (min t T)
  have hmap : Continuous (fun q : ℝ≥0 × State N => (min q.1 T, q.2)) :=
    (continuous_fst.min continuous_const).prodMk continuous_snd
  have hXc : Continuous (fun q : ℝ≥0 × State N => X q.1 q.2) := by
    change Continuous ((fun q : ℝ≥0 × State N =>
      stateClass (NullAugmentation.driver D₀) hb hs q.2 T q.1) ∘
      (fun q : ℝ≥0 × State N => (min q.1 T, q.2)))
    exact (FlowTerminalJointContinuity.stateClass_joint_continuous D₀
      hbg hsg hb hs hbd hsd T hT).comp hmap
  have hDXc : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (X q.1) q.2) := by
    have hh := (FlowTerminalJointContinuity.stateResponse_joint_continuous D₀
      hbg hsg hb hs hbd hsd hbd2 hsd2 T hT).comp hmap
    exact hh.congr (fun q => (congrFun
      (clampedState_fderiv D₀ hbg hsg hb hs hbd hsd T hT q.1) q.2).symm)
  have hDDXc : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (fderiv ℝ (X q.1)) q.2) := by
    have hh := (FlowTerminalHessianContinuity.response_second_fderiv_joint_continuous
      D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT).comp hmap
    exact hh.congr (fun q => by
      dsimp only [X, Function.comp_def]
      rw [clampedState_fderiv D₀ hbg hsg hb hs hbd hsd T hT q.1])
  let B : ℝ≥0 := ⟨FlowTerminalMomentBounds.fourthConstant N Kb Ks T ^ ((1 : ℝ) / 4),
    Real.rpow_nonneg (FlowTerminalMomentBounds.fourthConstant_nonneg N Kb Ks T) _⟩
  have h4 (t) (x y) : MemLp (X t y - X t x : Lp (State N) 2 P) 4 P :=
    (FlowTerminalMomentBounds.increment_terminal_fourthMoment D₀ hbg hsg hb hs
      x y T (min t T) hT (min_le_right _ _)).1
  have hfour (t) (x y) : lpNorm (X t y - X t x : Lp (State N) 2 P) 4 P ≤ B * ‖y - x‖ :=
    FlowTerminalLpSpatialBounds.increment_terminal_lpNorm_four_le D₀ hbg hsg hb hs
      x T (min t T) hT (min_le_right _ _) y
  obtain ⟨C0, hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨K0, hK0⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by norm_num))
  let C : ℝ≥0 := ⟨max C0 0, le_max_right _ _⟩
  let K : ℝ≥0 := ⟨max K0 0, le_max_right _ _⟩
  have hC : ∀ x, ‖f x‖ ≤ C := fun x => (hC0 x).trans (le_max_left _ _)
  have hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K := fun x => (hK0 x).trans (le_max_left _ _)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hfc.fderiv ℝ)
    (hf.fderiv_right (m := 1) (by norm_num)) (by norm_num)
  obtain ⟨M, hM⟩ := gradient_fderiv_bounded hf hfc
  have huc := gradient_fderiv_uniformContinuous hf hfc
  have hugc := gradient_uniformContinuous hf hfc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact observable_family_contDiff_two f hf C K L M hC hK hL hM huc (X t) (hX t)
      B (h4 t) (hfour t)
  · exact value_joint_continuous f hf C K L hC hK hL X hXc
  · exact first_joint_continuous f hf C K L hC hK hL hugc X hX hXc hDXc
  · exact second_joint_continuous f hf C K L M hC hK hL hM huc hugc
      X hX hXc hDXc hDDXc B h4 hfour

lemma clampedExpectation_eq_transition (f : State N → ℝ) (T t : ℝ≥0) (ht : t ≤ T) :
    clampedExpectation D₀ hb hs f T t =
      FixedCoefficients.transition (NullAugmentation.driver D₀) hb hs t f := by
  funext x
  unfold clampedExpectation observable clampedState
  rw [min_eq_left ht, FixedCoefficients.transition_eq_actual]
  apply integral_congr_ae
  filter_upwards [stateClass_ae (NullAugmentation.driver D₀) hb hs x T t,
    GlobalSDE.process_eq_horizon (NullAugmentation.driver D₀) hb hs x T] with omega hc hg
  exact congrArg f (hc.trans (hg t ht).symm)

include hbg hsg hbd hsd hbd2 hsd2 in
/-- Joint value/first/second jet regularity of the literal transition
expectation, on all nonnegative times and arbitrary initial states. -/
theorem transition_regular (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∀ t, ContDiff ℝ 2 (FixedCoefficients.transition (NullAugmentation.driver D₀) hb hs t f)) ∧
    Continuous (fun q : ℝ≥0 × State N => FixedCoefficients.transition
      (NullAugmentation.driver D₀) hb hs q.1 f q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => fderiv ℝ
      (FixedCoefficients.transition (NullAugmentation.driver D₀) hb hs q.1 f) q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => Hessian
      (FixedCoefficients.transition (NullAugmentation.driver D₀) hb hs q.1 f) q.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    have hT : 0 < t + 1 := by positivity
    have ht : t ≤ t + 1 := by simp
    rw [← clampedExpectation_eq_transition D₀ hb hs f (t + 1) t ht]
    exact (clampedExpectation_regular D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 f hf hfc (t + 1) hT).1 t
  · apply LocalHorizonContinuity.continuous_of_horizon_agreement _
      (fun T q => clampedExpectation D₀ hb hs f T q.1 q.2)
    · intro T hT
      exact (clampedExpectation_regular D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 f hf hfc T hT).2.1
    · intro T _ q hq
      exact (congrFun (clampedExpectation_eq_transition D₀ hb hs f T q.1 hq) q.2).symm
  · apply LocalHorizonContinuity.continuous_of_horizon_agreement _
      (fun T q => fderiv ℝ (clampedExpectation D₀ hb hs f T q.1) q.2)
    · intro T hT
      exact (clampedExpectation_regular D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 f hf hfc T hT).2.2.1
    · intro T _ q hq
      rw [clampedExpectation_eq_transition D₀ hb hs f T q.1 hq]
  · apply LocalHorizonContinuity.continuous_of_horizon_agreement _
      (fun T q => Hessian (clampedExpectation D₀ hb hs f T q.1) q.2)
    · intro T hT
      exact (clampedExpectation_regular D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 f hf hfc T hT).2.2.2
    · intro T _ q hq
      rw [clampedExpectation_eq_transition D₀ hb hs f T q.1 hq]

end Regularity

/-- The expectation of the literal actual mixed transition kernel. -/
def mixedExpectation (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (t : ℝ≥0) (f : State N → ℝ) (x : State N) : ℝ :=
  FixedCoefficients.transition (FixedCoefficients.canonicalDriver N)
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec t f x

theorem mixedExpectation_eq_actual (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (f : State N → ℝ) (x : State N) :
    mixedExpectation μ J β t f x = ∫ omega, f (mixedProcess μ J β x t omega) ∂VectorBrownian.law N :=
  FixedCoefficients.transition_eq_actual _ _ _ _ _ _

theorem mixedExpectation_eq_kernel (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f) (x : State N) :
    mixedExpectation μ J β t f x = ∫ y, f y ∂mixedTransitionKernel μ J β t x :=
  FixedCoefficients.transition_eq_kernel_integral _ _ _ _ _ hf _

/-- Smoothness of each actual mixed cutoff coordinate. -/
theorem mixedCutoff_contDiff (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (i : Fin N) :
    ContDiff ℝ ∞ (cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N) i) :=
  (VariationalCoefficients.coordinate i).contDiff.comp
    (cutoffCoefficient_contDiff _ (cutoffRadius_pos N) _
      ((contDiff_drift β _ (mixedGradient_contDiff μ J)).of_le (by simp)))

/-- Compact support of each actual mixed cutoff coordinate. -/
theorem mixedCutoff_hasCompactSupport (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (i : Fin N) :
    HasCompactSupport (cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N) i) :=
  (cutoffCoefficient_hasCompactSupport _ (cutoffRadius_pos N) (drift β (mixedGradient μ J))).comp_left
    (g := fun x : State N => x i) (by rfl)

/-- True global uniform first and second derivative Lipschitz bounds,
derived from smooth compact support of the literal mixed cutoff. -/
theorem mixedCutoff_derivative_bounds (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) :
    (∃ L : ℝ≥0, ∀ i : Fin N, LipschitzWith L
      (fderiv ℝ (cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N) i))) ∧
    (∃ M : ℝ≥0, ∀ i : Fin N, LipschitzWith M
      (fderiv ℝ (fderiv ℝ (cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N) i)))) := by
  classical
  constructor
  · have hi (i : Fin N) := ContDiff.lipschitzWith_of_hasCompactSupport
      ((mixedCutoff_hasCompactSupport μ J β i).fderiv ℝ)
      ((mixedCutoff_contDiff μ J β i).fderiv_right (m := ∞) (by simp)) (by simp)
    choose L hL using hi
    exact ⟨∑ i, L i, fun i => (hL i).weaken
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i))⟩
  · have hi (i : Fin N) := HamiltonianSecondCoefficientBounds.second_derivative_lipschitz
      (mixedCutoff_contDiff μ J β i) (mixedCutoff_hasCompactSupport μ J β i)
    choose M hM using hi
    exact ⟨∑ i, M i, fun i => (hM i).weaken
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i))⟩

/-- The actual mixed transition has genuine C² spatial slices and
continuous time/state value, gradient and Hessian jets. -/
theorem mixedExpectation_regular (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∀ t, ContDiff ℝ 2 (mixedExpectation μ J β t f)) ∧
    Continuous (fun q : ℝ≥0 × State N => mixedExpectation μ J β q.1 f q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (mixedExpectation μ J β q.1 f) q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => Hessian (mixedExpectation μ J β q.1 f) q.2) := by
  obtain ⟨⟨Lb, hb⟩, ⟨Mb, hb2⟩⟩ := mixedCutoff_derivative_bounds μ J β
  obtain ⟨Ls, hs⟩ := HamiltonianFlowDerivative.cutoffNoise_derivative_uniform_lipschitz
    (N := N) (cutoffRadius N) (cutoffRadius_pos N)
  obtain ⟨Ms, hs2⟩ := HamiltonianSecondCoefficientBounds.cutoffNoise_secondDerivative_uniform_lipschitz
    (N := N) (cutoffRadius N) (cutoffRadius_pos N)
  exact Regularity.transition_regular (VectorBrownian.driver N) (mixedCutoff_contDiff μ J β)
    (VariationalCoefficients.cutoffNoise_contDiff _ (cutoffRadius_pos N))
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec
    hb hs hb2 hs2 f hf hfc

namespace Ito
open VectorIto AnnealedSDECore PhysicalC2Ito MultivariateItoFormula

/-- The literal coefficient Itô generator of an arbitrary smooth spherical
potential gradient, with the actual √2 projection noise. -/
def coefficientGenerator (β : ℝ) (gfield : State N → State N)
    (f : State N → ℝ) (x : State N) : ℝ :=
  fderiv ℝ f x (drift β gfield x) +
    (1 / 2 : ℝ) * ∑ j : Fin N, Hessian f x (noiseColumn x j) (noiseColumn x j)

lemma generator_coordinates (β : ℝ) (gfield : State N → State N)
    (f : State N → ℝ) (x : State N) :
    coefficientGenerator β gfield f x =
      (∑ i : Fin N, fderiv ℝ f x (basisVector i) * drift β gfield x i) +
      (1 / 2 : ℝ) * (∑ i : Fin N, ∑ k : Fin N,
        Hessian f x (basisVector i) (basisVector k) *
          (∑ j : Fin N, noiseColumn x j i * noiseColumn x j k)) := by
  unfold coefficientGenerator
  rw [derivative_coordinates, noise_hessian_coordinates]

lemma generator_continuous (β : ℝ) (gfield : State N → State N)
    (hgfield : ContDiff ℝ ⊤ gfield) {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coefficientGenerator β gfield f) := by
  have hD := hf.continuous_fderiv (by norm_num)
  have hH := hessian_continuous hf
  unfold coefficientGenerator
  exact (hD.clm_apply (contDiff_drift β gfield hgfield).continuous).add
    ((continuous_finsetSum Finset.univ (fun j _ =>
      (hH.clm_apply (contDiff_noiseColumn j).continuous).clm_apply
        (contDiff_noiseColumn j).continuous)).const_mul _)

lemma generator_integral_coordinates (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ ⊤ gfield)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (g : ℝ≥0 → State N)
    (hg : Continuous g) (T : ℝ≥0) :
    (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,fderiv ℝ f (g s) (basisVector i)*
      drift β gfield (g s) i ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
      Hessian f (g s) (basisVector i) (basisVector k)*
        (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k) ∂nonnegativeLebesgueMeasure)=
    ∫ s in Ioc (0 : ℝ≥0) T,coefficientGenerator β gfield f (g s) ∂nonnegativeLebesgueMeasure := by
  let d (i : Fin N) (s : ℝ≥0) := fderiv ℝ f (g s) (basisVector i)*drift β gfield (g s) i
  let q (i k : Fin N) (s : ℝ≥0) := Hessian f (g s) (basisVector i) (basisVector k)*
    (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k)
  have hd (i : Fin N) : IntegrableOn (d i) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hc : Continuous (d i) := ((MultivariateItoWeights.derivative_basis_continuous hf i).comp hg).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp ((contDiff_drift β gfield hgfield).continuous.comp hg))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hq (i k : Fin N) : IntegrableOn (q i k) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hnoise (j a : Fin N) : Continuous (fun s => noiseColumn (g s) j a) :=
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) a).comp ((contDiff_noiseColumn j).continuous.comp hg)
    have hc : Continuous (q i k) := ((MultivariateItoSums.hessian_basis_continuous hf i k).comp hg).mul
      (continuous_finsetSum Finset.univ (fun j _ => (hnoise j i).mul (hnoise j k)))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hds := integrable_finsetSum Finset.univ (fun i _ => hd i)
  have hqs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun k _ => hq i k))
  change (∑ i,∫ s in Ioc (0 : ℝ≥0) T,d i s ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i,∑ k,∫ s in Ioc (0 : ℝ≥0) T,q i k s ∂nonnegativeLebesgueMeasure)=_
  calc
    _ = (∫ s in Ioc (0 : ℝ≥0) T,∑ i,d i s ∂nonnegativeLebesgueMeasure)+
      (1/2 : ℝ)*(∫ s in Ioc (0 : ℝ≥0) T,∑ i,∑ k,q i k s ∂nonnegativeLebesgueMeasure) := by
        rw [integral_finsetSum _ (fun i _ => hd i),
          integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hq i k))]
        congr 2
        exact Finset.sum_congr rfl (fun i _ => (integral_finsetSum _ (fun k _ => hq i k)).symm)
    _ = ∫ s in Ioc (0 : ℝ≥0) T,((∑ i,d i s)+(1/2 : ℝ)*(∑ i,∑ k,q i k s)) ∂nonnegativeLebesgueMeasure := by
      have he := integral_add hds (hqs.const_mul (1/2 : ℝ))
      rw [he,integral_const_mul]
    _ = _ := integral_congr_ae (.of_forall (fun s => (generator_coordinates β gfield f (g s)).symm))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine general C² Itô formula for the actual sphere Hamiltonian SDE,
with the actual physical coefficient generator rather than an assumed PDE. -/
theorem physical_C2_ito_formula (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ ⊤ gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i j,(V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s omega => fderiv ℝ f (X s omega) (basisVector i)*noiseColumn (X s omega) j i) T) ∧
      ∀ᵐ omega ∂P,f (X T omega)=f (Z0 omega)+
        (∫ s in Ioc (0 : ℝ≥0) T,coefficientGenerator β gfield f (X s omega) ∂nonnegativeLebesgueMeasure)+
        ∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) omega := by
  have hb : ∀ᵐ omega ∂P,∀ s,‖X s omega‖≤R := by
    filter_upwards [hXs] with omega homega
    intro s
    have hn : ‖X s omega‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using homega s
    nlinarith [norm_nonneg (X s omega)]
  obtain ⟨V,hV,he⟩ := strong_C2_ito_formula D T hX
    (fun _ i j => (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp (contDiff_noiseColumn j).continuous)
    R hR hb hf
  refine ⟨V,hV,?_⟩
  filter_upwards [he,hX.2.2.1] with omega heomega hc
  have hg := generator_integral_coordinates β gfield hgfield hf (fun s => X s omega) hc T
  linarith


open ActualC2Dynkin SharpRadialMoment PredictableDriftTime

theorem physical_C2_expectation_eq (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ ⊤ gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ omega,f (X T omega) ∂P)=(∫ omega,f (Z0 omega) ∂P)+
      ∫ s in (0 : ℝ)..(T : ℝ),∫ omega,coefficientGenerator β gfield f (X s.toNNReal omega) ∂P := by
  obtain ⟨V,hV,he⟩ := physical_C2_ito_formula D β gfield hgfield T hX hXs R hR hNR hf
  let G : ℝ≥0 → Ω → ℝ := fun s omega => coefficientGenerator β gfield f (X s omega)
  have hGa : StronglyAdapted F G := fun s => (generator_continuous β gfield hgfield hf).comp_stronglyMeasurable (hX.2.1 s)
  have hGc : ∀ᵐ omega ∂P,Continuous (fun s => G s omega) := hX.2.2.1.mono
    (fun _ hc => (generator_continuous β gfield hgfield hf).comp hc)
  obtain ⟨Kg,hKg⟩ := sphere_observable_bound _ (generator_continuous β gfield hgfield hf) R hR hNR X hXs
  obtain ⟨Kf,hKf⟩ := sphere_observable_bound f hf.continuous R hR hNR X hXs
  have hf0 : Integrable (fun omega => f (X 0 omega)) P := Integrable.of_bound
    (hf.continuous.comp_aestronglyMeasurable (((hX.2.1 0).mono (F.le 0)).aestronglyMeasurable)) Kf
    (hKf.mono (fun _ h => h 0))
  have hfZ : Integrable (fun omega => f (Z0 omega)) P := hf0.congr
    ((randomStrong_initial_ae D T hX).mono (fun _ h => congrArg f h))
  have hGI : Integrable (fun omega => ∫ s in Ioc (0 : ℝ≥0) T,G s omega ∂nonnegativeLebesgueMeasure) P := by
    have hi := (timeCut_integrable G hGa hGc Kg hKg T).integral_prod_right
    convert hi using 1
    funext omega
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> simp [Set.indicator,FourPapersCommon.continuousAdaptedTimeCut,hs])
  have hnoise := integrable_finsetSum Finset.univ
    (fun i _ => (Lp.memLp (vectorIto D (V i))).integrable (by norm_num))
  rw [integral_congr_ae he]
  have hsum := integral_add (hfZ.add hGI) hnoise
  have hfirst := integral_add hfZ hGI
  simp only [Pi.add_apply] at hsum hfirst
  rw [hsum,hfirst,integral_finsetSum _ (fun i _ => (Lp.memLp (vectorIto D (V i))).integrable (by norm_num))]
  simp only [vectorIto_expectation_zero,Finset.sum_const_zero,add_zero]
  congr 1
  exact expectation_time_integral G hGa hGc Kg hKg T

/-- True generator evolution for every C² observable on the actual
physical sphere process, with no backward PDE assumed. -/
theorem physical_C2_hasDerivAt (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ ⊤ gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ∫ omega,f (X s.toNNReal omega) ∂P)
      (∫ omega,coefficientGenerator β gfield f (X t.toNNReal omega) ∂P) t := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β gfield hgfield hf) R hR hNR X hXs
  have hmean : Continuous (fun s : ℝ => ∫ omega,coefficientGenerator β gfield f (X s.toNNReal omega) ∂P) :=
    (firstMoment_continuous (P := P) (fun s omega => coefficientGenerator β gfield f (X s omega))
      (fun s => (generator_continuous β gfield hgfield hf).comp_stronglyMeasurable ((hX 0).2.1 s))
      ((hX 0).2.2.1.mono (fun _ hc => (generator_continuous β gfield hgfield hf).comp hc)) K hK).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) t) (hmean.stronglyMeasurableAtFilter volume (𝓝 t))
    hmean.continuousAt).const_add (∫ omega,f (Z0 omega) ∂P)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [physical_C2_expectation_eq D β gfield hgfield s.toNNReal (hX s.toNNReal) hXs R hR hNR hf,
    Real.coe_toNNReal _ hs.le]


theorem physical_C2_hasDerivWithinAt_zero (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ ⊤ gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => ∫ omega,f (X s.toNNReal omega) ∂P)
      (∫ omega,coefficientGenerator β gfield f (Z0 omega) ∂P) (Ici 0) 0 := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β gfield hgfield hf) R hR hNR X hXs
  have hmean : Continuous (fun s : ℝ => ∫ omega,coefficientGenerator β gfield f (X s.toNNReal omega) ∂P) :=
    (firstMoment_continuous (P := P) (fun s omega => coefficientGenerator β gfield f (X s omega))
      (fun s => (generator_continuous β gfield hgfield hf).comp_stronglyMeasurable ((hX 0).2.1 s))
      ((hX 0).2.2.1.mono (fun _ hc => (generator_continuous β gfield hgfield hf).comp hc)) K hK).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) 0) (hmean.stronglyMeasurableAtFilter volume (𝓝 0))
    hmean.continuousAt).const_add (∫ omega,f (Z0 omega) ∂P)
  have he : (∫ omega,coefficientGenerator β gfield f (X (Real.toNNReal 0) omega) ∂P)=
      ∫ omega,coefficientGenerator β gfield f (Z0 omega) ∂P := by
    rw [Real.toNNReal_zero]
    apply integral_congr_ae
    filter_upwards [randomStrong_initial_ae D 0 (hX 0)] with omega homega
    rw [homega]
  rw [he] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [physical_C2_expectation_eq D β gfield hgfield s.toNNReal (hX s.toNNReal) hXs R hR hNR hf,
      Real.coe_toNNReal _ hs]
  · rw [Real.toNNReal_zero,physical_C2_expectation_eq D β gfield hgfield 0 (hX 0) hXs R hR hNR hf]
    simp


end Ito

/-- Exact physical coefficient generator for the actual mixed field. -/
def mixedGenerator (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : State N → ℝ) : State N → ℝ := Ito.coefficientGenerator β (mixedGradient μ J) f

/-- Exact manuscript generator formula on the physical sphere,
with genuine Fréchet derivatives and the actual mixed Gaussian field. -/
theorem mixedGenerator_formula (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : State N → ℝ)
    (x : State N) (hx : OnSphere x) :
    mixedGenerator μ J β f x =
      (∑ i : Fin N, ∑ k : Fin N, ((if i = k then 1 else 0) - x i * x k / N) *
        fderiv ℝ (fderiv ℝ f) x (basisVector i) (basisVector k)) -
      kappa N * ⟪x, gradient f x⟫_ℝ +
      β * ⟪projection x (gradient (fieldOfMixture μ J) x), projection x (gradient f x)⟫_ℝ := by
  unfold mixedGenerator Ito.coefficientGenerator
  rw [SphereGenerator.hessian_noise_contraction hN x hx,
    SphereGenerator.gradient_drift_pairing hN x hx]
  unfold Hessian mixedGradient
  ring

/-- The actual untruncated mixed SDE realizes the genuine random-strong
solution interface used by the multivariate Itô provider. -/
theorem mixedProcess_randomStrongSolution (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    AnnealedSDECore.IsRandomStrongSolutionOn (FixedCoefficients.canonicalDriver N)
      (fun _ i z => mixedDrift μ J β z i) (fun _ i j z => noiseColumn z j i)
      (fun _ => x) (mixedProcess μ J β x) T :=
  RandomSDEConversions.localStrongSolution_to_random
    (fun i => (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp
      (contDiff_drift β _ (mixedGradient_contDiff μ J)).continuous)
    (mixedProcess_physical hN μ J β x hx T)

/-- Actual C² Dynkin formula of the literal mixed transition. -/
theorem mixedExpectation_dynkin (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (T : ℝ≥0) :
    mixedExpectation μ J β T f x = f x +
      ∫ s in (0 : ℝ)..(T : ℝ), mixedExpectation μ J β s.toNNReal (mixedGenerator μ J β f) x := by
  simp only [mixedExpectation_eq_actual]
  simpa only [integral_const, probReal_univ, one_smul, mixedGenerator] using
    Ito.physical_C2_expectation_eq (FixedCoefficients.canonicalDriver N) β
      (mixedGradient μ J) (mixedGradient_contDiff μ J) T
      (mixedProcess_randomStrongSolution hN μ J β x hx T)
      (mixedProcess_onSphere hN μ J β x hx) (cutoffRadius N) (cutoffRadius_pos N)
      (cutoffRadius_contains_sphere N) hf

/-- Actual positive-time derivative of the genuine mixed transition. -/
theorem mixedExpectation_hasDerivAt (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => mixedExpectation μ J β s.toNNReal f x)
      (mixedExpectation μ J β t.toNNReal (mixedGenerator μ J β f) x) t := by
  simp only [mixedExpectation_eq_actual]
  exact Ito.physical_C2_hasDerivAt (FixedCoefficients.canonicalDriver N) β
    (mixedGradient μ J) (mixedGradient_contDiff μ J)
    (fun T => mixedProcess_randomStrongSolution hN μ J β x hx T)
    (mixedProcess_onSphere hN μ J β x hx) (cutoffRadius N) (cutoffRadius_pos N)
    (cutoffRadius_contains_sphere N) hf t ht

/-- The literal mixed transition has the exact physical generator as
its right derivative at time zero. -/
theorem mixedExpectation_hasDerivWithinAt_zero (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => mixedExpectation μ J β s.toNNReal f x)
      (mixedGenerator μ J β f x) (Ici 0) 0 := by
  simp only [mixedExpectation_eq_actual]
  simpa only [integral_const, probReal_univ, one_smul, mixedGenerator] using
    Ito.physical_C2_hasDerivWithinAt_zero (FixedCoefficients.canonicalDriver N) β
      (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (fun T => mixedProcess_randomStrongSolution hN μ J β x hx T)
      (mixedProcess_onSphere hN μ J β x hx) (cutoffRadius N) (cutoffRadius_pos N)
      (cutoffRadius_contains_sphere N) hf

/-- Expectation Chapman–Kolmogorov for the literal mixed transition. -/
theorem mixedExpectation_semigroup (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (s t : ℝ≥0) (f : State N → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) (x : State N) :
    mixedExpectation μ J β (s + t) f x =
      mixedExpectation μ J β s (mixedExpectation μ J β t f) x :=
  FixedCoefficients.transition_semigroup
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec
    (mixedCoefficientBounds μ J β) s t f hf C hC x

/-- True generator commutation of the actual mixed transition; spatial
C² regularity of its transition observable is already derived above. -/
theorem mixedExpectation_generator_commutes (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) (ht : 0 < t) :
    mixedGenerator μ J β (mixedExpectation μ J β t.toNNReal f) x =
      mixedExpectation μ J β t.toNNReal (mixedGenerator μ J β f) x := by
  let g := mixedExpectation μ J β t.toNNReal f
  have hg : ContDiff ℝ 2 g := (mixedExpectation_regular μ J β hf hfc).1 t.toNNReal
  have hzero := mixedExpectation_hasDerivWithinAt_zero hN μ J β x hx hg
  have hd := mixedExpectation_hasDerivAt hN μ J β x hx hf t ht
  have hshift : HasDerivAt (fun s : ℝ => mixedExpectation μ J β (s + t).toNNReal f x)
      (mixedExpectation μ J β t.toNNReal (mixedGenerator μ J β f) x) 0 := by
    have hline : HasDerivAt (fun s : ℝ => s + t) 1 0 := (hasDerivAt_id (0 : ℝ)).add_const t
    have hd' : HasDerivAt (fun s : ℝ => mixedExpectation μ J β s.toNNReal f x)
        (mixedExpectation μ J β t.toNNReal (mixedGenerator μ J β f) x) (0 + t) := by
      simpa only [zero_add] using hd
    simpa only [Function.comp_def, mul_one] using hd'.comp 0 hline
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hsame (s : ℝ) (hs : s ∈ Ici 0) :
      mixedExpectation μ J β s.toNNReal g x = mixedExpectation μ J β (s + t).toNNReal f x := by
    have hck := mixedExpectation_semigroup μ J β s.toNNReal t.toNNReal f hf.continuous C hC x
    rw [← Real.toNNReal_add hs ht.le] at hck
    exact hck.symm
  have hright : HasDerivWithinAt (fun s : ℝ => mixedExpectation μ J β s.toNNReal g x)
      (mixedExpectation μ J β t.toNNReal (mixedGenerator μ J β f) x) (Ici 0) 0 := by
    apply hshift.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hsame s hs
    · exact hsame 0 self_mem_Ici
  have he := (uniqueDiffOn_Ici 0).eq self_mem_Ici hzero hright
  have he1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) he
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] using he1

/-- The actual mixed transition satisfies the genuine backward generator
identity, with no regularity or backward PDE premise. -/
theorem mixedExpectation_backward (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => mixedExpectation μ J β s.toNNReal f x)
      (mixedGenerator μ J β (mixedExpectation μ J β t.toNNReal f) x) t := by
  rw [mixedExpectation_generator_commutes hN μ J β x hx hf hfc t ht]
  exact mixedExpectation_hasDerivAt hN μ J β x hx hf t ht

/-- Real-time extension used solely to state ordinary derivative theorems. -/
def realExpectation (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : State N → ℝ) (t : ℝ) (x : State N) : ℝ :=
  mixedExpectation μ J β t.toNNReal f x

theorem realExpectation_contDiff (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ) :
    ContDiff ℝ 2 (realExpectation μ J β f t) :=
  (mixedExpectation_regular μ J β hf hfc).1 t.toNNReal

theorem realExpectation_joint_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (Function.uncurry (realExpectation μ J β f)) :=
  (mixedExpectation_regular μ J β hf hfc).2.1.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

/-- Actual generator jets of the mixed transition are jointly continuous;
this follows from the actual stochastic flow jets and literal coefficients. -/
theorem realExpectation_generator_joint_continuous (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun q : ℝ × State N => mixedGenerator μ J β
      (realExpectation μ J β f q.1) q.2) := by
  have hmap : Continuous (fun q : ℝ × State N => (q.1.toNNReal, q.2)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  have hD := (mixedExpectation_regular μ J β hf hfc).2.2.1.comp hmap
  have hH := (mixedExpectation_regular μ J β hf hfc).2.2.2.comp hmap
  have hb : Continuous (fun q : ℝ × State N => mixedDrift μ J β q.2) :=
    (contDiff_drift β _ (mixedGradient_contDiff μ J)).continuous.comp continuous_snd
  have hs (j : Fin N) : Continuous (fun q : ℝ × State N => noiseColumn q.2 j) :=
    (contDiff_noiseColumn j).continuous.comp continuous_snd
  exact (hD.clm_apply hb).add ((continuous_finsetSum Finset.univ
    (fun j _ => (hH.clm_apply (hs j)).clm_apply (hs j))).const_mul (1 / 2 : ℝ))

@[simp] theorem realExpectation_zero (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (f : State N → ℝ) (x : State N) : realExpectation μ J β f 0 x = f x := by
  simp only [realExpectation, Real.toNNReal_zero, mixedExpectation_eq_actual]
  exact integral_eq_const ((mixedProcess_zero μ J β x).mono (fun _ h => congrArg f h))

namespace CompactMeasure

/-- Continuity of a parameter integral against an actual finite measure
concentrated on a proved compact set. -/
theorem continuous_integral (ν : Measure (State N)) [IsFiniteMeasure ν]
    (K : Set (State N)) (hK : IsCompact K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    {f : ℝ → State N → ℝ} (hf : Continuous (Function.uncurry f)) :
    Continuous (fun t => ∫ x, f t x ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (t₀ - 1) (t₀ + 1))).prod hK).bddAbove_image
    hf.norm.continuousOn
  have hs : Icc (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · exact Eventually.of_forall (fun t =>
      (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · filter_upwards [hs] with t ht
    filter_upwards [hν] with x hx
    exact hM ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  · exact integrable_const M
  · exact ae_of_all _ (fun x =>
      (hf.comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- Local differentiation under an actual compactly supported finite law.
The pointwise derivatives need hold only on the proved support and the
open interpolation interval. -/
theorem hasDerivAt_integral (ν : Measure (State N)) [IsFiniteMeasure ν]
    (K : Set (State N)) (hK : IsCompact K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    {f f' : ℝ → State N → ℝ}
    (hf : Continuous (Function.uncurry f)) (hf' : Continuous (Function.uncurry f'))
    (a b z : ℝ) (ha : a < z) (hb : z < b)
    (hd : ∀ t ∈ Ioo a b, ∀ x ∈ K, HasDerivAt (fun s => f s x) (f' t x) t) :
    HasDerivAt (fun t => ∫ x, f t x ∂ν) (∫ x, f' z x ∂ν) z := by
  let l := (a + z) / 2
  let u := (z + b) / 2
  have hl : a < l := by dsimp [l]; linarith
  have hu : u < b := by dsimp [u]; linarith
  have hs : Icc l u ∈ 𝓝 z := Icc_mem_nhds (by dsimp [l]; linarith) (by dsimp [u]; linarith)
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc l u)).prod hK).bddAbove_image
    hf'.norm.continuousOn
  have hi : Integrable (f z) ν := by
    have hc : Continuous (f z) := hf.comp (continuous_const.prodMk continuous_id)
    simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] using
      hc.continuousOn.integrableOn_compact hK (μ := ν)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := f) (F' := f') (bound := fun _ => M) (x₀ := z) (s := Icc l u) hs
    (Eventually.of_forall (fun t =>
      (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)) hi
    (hf'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (by
      filter_upwards [hν] with x hx t ht
      exact hM ⟨(t, x), ⟨ht, hx⟩, rfl⟩)
    (integrable_const M)
    (hν.mono (fun x hx t ht => hd t ⟨hl.trans_le ht.1, ht.2.trans_lt hu⟩ x hx))).2

end CompactMeasure

/-- The actual physical support is a compact Euclidean sphere. -/
theorem physicalSphere_compact (N : ℕ) : IsCompact {x : State N | OnSphere x} := by
  have he : {x : State N | OnSphere x} = Metric.sphere (0 : State N) (Real.sqrt N) := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
    constructor
    · exact fun hx => SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
    · intro hx
      apply (onSphere_iff_norm_sq x).mpr
      rw [hx, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [he]
  exact isCompact_sphere _ _

/-- Actual detailed-balance interpolation in the normalized mixed Gibbs law. -/
def gibbsInterpolation (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f g : State N → ℝ) (t z : ℝ) : ℝ :=
  ∫ x, realExpectation μ J β f (t - z) x * realExpectation μ J β g z x
    ∂mixtureGibbsLaw μ β J

/-- The interpolation is continuous, including both endpoints. -/
theorem gibbsInterpolation_continuous (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f g : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ) :
    Continuous (gibbsInterpolation μ J β f g t) := by
  let := mixtureGibbsLaw_probability hN μ β J
  apply CompactMeasure.continuous_integral (mixtureGibbsLaw μ β J)
    {x : State N | OnSphere x} (physicalSphere_compact N)
    ((gibbsLaw_support hN β (fieldOfMixture μ J)).mono (fun x hx =>
      (onSphere_iff_norm_sq x).mpr hx))
  exact ((realExpectation_joint_continuous μ J β hf hfc).comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)).mul
      (realExpectation_joint_continuous μ J β hg hgc)

/-- Exact identification of the actual mixed Itô generator and the actual
spherical rotation generator, on the physical sphere. -/
theorem mixedGenerator_eq_rotationGenerator (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (x : State N) (hx : OnSphere x) :
    mixedGenerator μ J β f x = SphericalForm.rotationGenerator N β (fieldOfMixture μ J) f x :=
  (SphericalForm.rotationGenerator_eq_coefficientGenerator hN β (fieldOfMixture μ J) hf x hx).symm

/-- Symmetry of the literal mixed coefficient generator against its actual
normalized Gibbs law, derived from actual spherical integration by parts. -/
theorem mixedGenerator_symmetric (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f g : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x, f x * mixedGenerator μ J β g x ∂mixtureGibbsLaw μ β J) =
      ∫ x, g x * mixedGenerator μ J β f x ∂mixtureGibbsLaw μ β J := by
  calc
    _ = ∫ x, f x * SphericalForm.rotationGenerator N β (fieldOfMixture μ J) g x
        ∂mixtureGibbsLaw μ β J := by
      apply integral_congr_ae
      filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
      rw [mixedGenerator_eq_rotationGenerator (by omega) μ J β hg x
        ((onSphere_iff_norm_sq x).mpr hx)]
    _ = ∫ x, g x * SphericalForm.rotationGenerator N β (fieldOfMixture μ J) f x
        ∂mixtureGibbsLaw μ β J :=
      SphericalForm.rotationGenerator_symmetric hN β
        ((fieldOfMixture_contDiff μ J).of_le (by simp)) hf hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
      rw [mixedGenerator_eq_rotationGenerator (by omega) μ J β hf x
        ((onSphere_iff_norm_sq x).mpr hx)]

/-- The actual detailed-balance interpolation has derivative zero in its
interior. Both backward PDE identities and Gibbs symmetry have been proved. -/
theorem gibbsInterpolation_hasDerivAt_zero (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f g : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t z : ℝ) (hz : 0 < z) (hzt : z < t) :
    HasDerivAt (gibbsInterpolation μ J β f g t) 0 z := by
  let := mixtureGibbsLaw_probability hN μ β J
  let Fv := realExpectation μ J β f
  let Gv := realExpectation μ J β g
  let Iv : ℝ → State N → ℝ := fun r x => Fv (t - r) x * Gv r x
  let Id : ℝ → State N → ℝ := fun r x =>
    -(mixedGenerator μ J β (Fv (t - r)) x) * Gv r x +
      Fv (t - r) x * mixedGenerator μ J β (Gv r) x
  have hF : Continuous (Function.uncurry Fv) := realExpectation_joint_continuous μ J β hf hfc
  have hG : Continuous (Function.uncurry Gv) := realExpectation_joint_continuous μ J β hg hgc
  have hLF : Continuous (fun q : ℝ × State N => mixedGenerator μ J β (Fv q.1) q.2) :=
    realExpectation_generator_joint_continuous μ J β hf hfc
  have hLG : Continuous (fun q : ℝ × State N => mixedGenerator μ J β (Gv q.1) q.2) :=
    realExpectation_generator_joint_continuous μ J β hg hgc
  have hmap : Continuous (fun q : ℝ × State N => (t - q.1, q.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hIv : Continuous (Function.uncurry Iv) := (hF.comp hmap).mul hG
  have hId : Continuous (Function.uncurry Id) :=
    ((hLF.comp hmap).neg.mul hG).add ((hF.comp hmap).mul hLG)
  have hd := CompactMeasure.hasDerivAt_integral (mixtureGibbsLaw μ β J)
    {x : State N | OnSphere x} (physicalSphere_compact N)
    ((gibbsLaw_support hN β (fieldOfMixture μ J)).mono (fun x hx =>
      (onSphere_iff_norm_sq x).mpr hx)) hIv hId 0 t z hz hzt (by
      intro r hr x hx
      have hr0 : 0 < r := hr.1
      have htr : 0 < t - r := sub_pos.mpr hr.2
      have hdF := (mixedExpectation_backward (by omega) μ J β x hx hf hfc (t - r) htr).comp
        r ((hasDerivAt_id r).const_sub t)
      have hdG := mixedExpectation_backward (by omega) μ J β x hx hg hgc r hr0
      have hdf : HasDerivAt (fun s => Fv (t - s) x)
          (-mixedGenerator μ J β (Fv (t - r)) x) r := by
        dsimp only [Fv, realExpectation]
        convert hdF using 1 <;> (try simp only [Function.comp_def, mul_neg_one])
        rfl
      exact hdf.mul hdG)
  have hFz : ContDiff ℝ 2 (Fv (t - z)) := realExpectation_contDiff μ J β hf hfc _
  have hGz : ContDiff ℝ 2 (Gv z) := realExpectation_contDiff μ J β hg hgc _
  have hSym := mixedGenerator_symmetric hN μ J β hFz hGz
  have hi1 : Integrable (fun x => mixedGenerator μ J β (Fv (t - z)) x * Gv z x)
      (mixtureGibbsLaw μ β J) := SphericalForm.integrable_gibbs_of_continuous hN β
    (fieldOfMixture_contDiff μ J).continuous
    ((Ito.generator_continuous β _ (mixedGradient_contDiff μ J) hFz).mul hGz.continuous)
  have hi2 : Integrable (fun x => Fv (t - z) x * mixedGenerator μ J β (Gv z) x)
      (mixtureGibbsLaw μ β J) := SphericalForm.integrable_gibbs_of_continuous hN β
    (fieldOfMixture_contDiff μ J).continuous
    (hFz.continuous.mul (Ito.generator_continuous β _ (mixedGradient_contDiff μ J) hGz))
  have hcomm : (∫ x, mixedGenerator μ J β (Fv (t - z)) x * Gv z x ∂mixtureGibbsLaw μ β J) =
      ∫ x, Gv z x * mixedGenerator μ J β (Fv (t - z)) x ∂mixtureGibbsLaw μ β J := by
    apply integral_congr_ae
    exact .of_forall (fun x => mul_comm _ _)
  have hzero : (∫ x, Id z x ∂mixtureGibbsLaw μ β J) = 0 := by
    dsimp [Id]
    simp_rw [neg_mul]
    rw [integral_add (f := fun x => -(mixedGenerator μ J β (Fv (t - z)) x * Gv z x))
      (g := fun x => Fv (t - z) x * mixedGenerator μ J β (Gv z) x)
      hi1.neg hi2, integral_neg, hcomm, ← hSym]
    ring
  rw [hzero] at hd
  exact hd

/-- Genuine detailed balance of the literal mixed SDE for compact C²
observables, derived by the actual backward interpolation. -/
theorem compact_mixedExpectation_reversible (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f g : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ≥0) :
    (∫ x, mixedExpectation μ J β t f x * g x ∂mixtureGibbsLaw μ β J) =
      ∫ x, f x * mixedExpectation μ J β t g x ∂mixtureGibbsLaw μ β J := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
    (gibbsInterpolation_continuous hN μ J β hf hfc hg hgc t).continuousOn
    (fun z hz => gibbsInterpolation_hasDerivAt_zero hN μ J β hf hfc hg hgc t z hz.1 hz.2)
    ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).intervalIntegrable 0 t)
  simp only [intervalIntegral.integral_zero, gibbsInterpolation, sub_self, sub_zero,
    realExpectation_zero] at hh
  simpa only [realExpectation, Real.toNNReal_coe] using (sub_eq_zero.mp hh.symm).symm

/-- The actual mixed Gibbs measure is supported on the physical sphere. -/
theorem mixtureGibbsLaw_onSphere (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    ∀ᵐ x ∂mixtureGibbsLaw μ β J, OnSphere x :=
  (gibbsLaw_support hN β (fieldOfMixture μ J)).mono
    (fun x hx => (onSphere_iff_norm_sq x).mpr hx)

/-- Sphere-constant tests remain constant under the literal actual SDE. -/
theorem mixedExpectation_const_onSphere (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (f : State N → ℝ) (c : ℝ)
    (hf : ∀ y, OnSphere y → f y = c) (x : State N) (hx : OnSphere x) :
    mixedExpectation μ J β t f x = c := by
  rw [mixedExpectation_eq_actual]
  apply integral_eq_const
  filter_upwards [mixedProcess_onSphere hN μ J β x hx] with omega homega
  exact hf _ (homega t)

/-- Genuine compact-test invariance in the actual mixed Gibbs law,
obtained from the proved transition balance and actual sphere preservation. -/
theorem compact_mixedExpectation_stationary (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    (∫ x, mixedExpectation μ J β t f x ∂mixtureGibbsLaw μ β J) =
      ∫ x, f x ∂mixtureGibbsLaw μ β J := by
  let bump := coefficientBump (N := N) ((N : ℝ) + 1) (by positivity)
  have hb : ContDiff ℝ 2 (fun x : State N => bump x) := bump.contDiff
  have hh := compact_mixedExpectation_reversible hN μ J β hb bump.hasCompactSupport hf hfc t
  have hleft : (∫ x, mixedExpectation μ J β t bump x * f x ∂mixtureGibbsLaw μ β J) =
      ∫ x, f x ∂mixtureGibbsLaw μ β J := by
    apply integral_congr_ae
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
    rw [mixedExpectation_const_onSphere (by omega) μ J β t bump 1
      (fun y hy => SphereSmoothTestMeasureExt.coefficientBump_one_onSphere hy) x hx, one_mul]
  have hright : (∫ x, bump x * mixedExpectation μ J β t f x ∂mixtureGibbsLaw μ β J) =
      ∫ x, mixedExpectation μ J β t f x ∂mixtureGibbsLaw μ β J := by
    apply integral_congr_ae
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
    rw [SphereSmoothTestMeasureExt.coefficientBump_one_onSphere hx, one_mul]
  rw [hleft, hright] at hh
  exact hh.symm

/-- The genuine law obtained by evolving independent Gibbs initial data
through the constructed mixed Langevin transition kernel. -/
def mixedGibbsWaitingLaw (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : Measure (State N) :=
  mixedTransitionKernel μ J β t ∘ₘ mixtureGibbsLaw μ β J

theorem mixedGibbsWaitingLaw_probability (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (mixedGibbsWaitingLaw μ J β t) := by
  let := mixtureGibbsLaw_probability hN μ β J
  unfold mixedGibbsWaitingLaw
  infer_instance

/-- Sphere support of the actual Gibbs-initial terminal law is derived
from the genuine transition support and initial Gibbs support. -/
theorem mixedGibbsWaitingLaw_onSphere (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    ∀ᵐ x ∂mixedGibbsWaitingLaw μ J β t, OnSphere x := by
  apply Measure.ae_comp_of_ae_ae (sphere_measurableSet N)
  filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
  rw [mixedTransitionKernel_apply, mixedTransitionLaw]
  exact (ae_map_iff (mixedProcess_measurable μ J β x t).aemeasurable
    (sphere_measurableSet N)).2
      ((mixedProcess_onSphere (by omega) μ J β x hx).mono (fun _ h => h t))

/-- Compact-observable integrals against the genuine Gibbs-initial law
are exactly the actual transition expectations in the genuine initial law. -/
theorem mixedGibbsWaitingLaw_integral (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f : State N → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    (∫ y, f y ∂mixedGibbsWaitingLaw μ J β t) =
      ∫ x, mixedExpectation μ J β t f x ∂mixtureGibbsLaw μ β J := by
  let := mixtureGibbsLaw_probability hN μ β J
  let := mixedGibbsWaitingLaw_probability hN μ J β t
  have hi : Integrable f (mixedGibbsWaitingLaw μ J β t) :=
    hf.integrable_of_hasCompactSupport hfc
  rw [mixedGibbsWaitingLaw, Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, Kernel.const_apply]
  apply integral_congr_ae
  exact .of_forall (fun x => (mixedExpectation_eq_kernel μ J β t f hf.stronglyMeasurable x).symm)

/-- Full literal Gibbs invariance of the actual finite mixed diffusion.
Equality of the entire probability laws follows from genuine compact C²
test characterization, actual support, and proved compact-test balance. -/
theorem mixedGibbsLaw_stationary (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    mixedGibbsWaitingLaw μ J β t = mixtureGibbsLaw μ β J := by
  let := mixtureGibbsLaw_probability hN μ β J
  let := mixedGibbsWaitingLaw_probability hN μ J β t
  apply SphereSmoothTestMeasureExt.measure_eq_of_compactC2_integrals
    (mixedGibbsWaitingLaw_onSphere hN μ J β t) (mixtureGibbsLaw_onSphere hN μ J β)
  intro f hf hfc
  rw [mixedGibbsWaitingLaw_integral hN μ J β hf.continuous hfc t]
  exact compact_mixedExpectation_stationary hN μ J β hf hfc t

/-- Literal invariance of the normalized mixed Gibbs law under the actual
measurable Markov kernel, with unrestricted finite mixture parity. -/
theorem mixedTransitionKernel_gibbs_invariant (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    mixedTransitionKernel μ J β t ∘ₘ mixtureGibbsLaw μ β J = mixtureGibbsLaw μ β J :=
  mixedGibbsLaw_stationary hN μ J β t

end SlowEquilibration.SphericalReversibility
