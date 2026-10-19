-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetConcentration
public import SlowEquilibration.SourcePhysicalPairSphereActualJetBounds
public import SphericalAging.HamiltonianParameter

/-!
The regularity estimates in manuscript `lem:pc-regularity` for the amplitude-one
pure model: the actual ball gradient supremum is p-Lipschitz in Euclidean
disorder and has expectation of order sqrt N. On the original measurable
`regularDisorder` event, whose complement has probability at most exp(-N),
the full covariant spherical third derivative is of order 1 / sqrt N.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureHighEnergyRegularity

open MeasureTheory ProbabilityTheory Set SphericalModel
open PureTensorJetBounds PureTensorJetConcentration PairConditionalDeterminantMoments
open scoped BigOperators RealInnerProductSpace NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual ambient gradient supremum on the physical ball. -/
def ballGradientSup {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) : ℝ :=
  sSup ((fun x : Vector N => ‖gradient (field c J) x‖) ''
    Metric.closedBall 0 (Real.sqrt (N : ℝ)))

private def tensorBallGradientSup {N p : ℕ}
    (J : SphericalAging.FiniteModel.Disorder N p) : ℝ :=
  sSup ((fun x : Vector N =>
    ‖gradient (SphericalAging.FiniteModel.Hamiltonian N p J) x‖) ''
      Metric.closedBall 0 (Real.sqrt (N : ℝ)))

private lemma gradient_norm_le_envelope {N p : ℕ} (hN : 0 < N)
    (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N)
    (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) :
    ‖gradient (SphericalAging.FiniteModel.Hamiltonian N p J) x‖ ≤
      pureJetEnvelope N p 1 J := by
  rw [gradient, LinearIsometryEquiv.norm_map, ← norm_iteratedFDeriv_one]
  exact iteratedFDeriv_norm_le_pureJetEnvelope hN J x hx

private lemma tensorGradient_bddAbove {N p : ℕ} (hN : 0 < N)
    (J : SphericalAging.FiniteModel.Disorder N p) :
    BddAbove ((fun x : Vector N =>
      ‖gradient (SphericalAging.FiniteModel.Hamiltonian N p J) x‖) ''
        Metric.closedBall 0 (Real.sqrt (N : ℝ))) := by
  refine ⟨pureJetEnvelope N p 1 J, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact gradient_norm_le_envelope hN J x (by simpa using hx)

private lemma tensorBallGradientSup_nonneg {N p : ℕ} (hN : 0 < N)
    (J : SphericalAging.FiniteModel.Disorder N p) :
    0 ≤ tensorBallGradientSup J := by
  exact (norm_nonneg _).trans (le_csSup (tensorGradient_bddAbove hN J)
    ⟨0, Metric.mem_closedBall_self (Real.sqrt_nonneg _), rfl⟩)

private lemma tensorBallGradientSup_le_envelope {N p : ℕ} (hN : 0 < N)
    (J : SphericalAging.FiniteModel.Disorder N p) :
    tensorBallGradientSup J ≤ pureJetEnvelope N p 1 J := by
  unfold tensorBallGradientSup
  refine csSup_le ⟨_, ⟨0, Metric.mem_closedBall_self (Real.sqrt_nonneg _), rfl⟩⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact gradient_norm_le_envelope hN J x (by simpa using hx)

private lemma tensor_gradient_sub {N p : ℕ}
    (J K : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) :
    gradient (SphericalAging.FiniteModel.Hamiltonian N p (J - K)) x =
      gradient (SphericalAging.FiniteModel.Hamiltonian N p J) x -
        gradient (SphericalAging.FiniteModel.Hamiltonian N p K) x := by
  have h := SphericalAging.HamiltonianParameter.gradient_add J (-K)
  rw [show J + (-K) = J - K from rfl, show -K = (-1 : ℝ) • K by simp,
    SphericalAging.HamiltonianParameter.gradient_smul] at h
  simpa only [SphericalAging.HardSphereDynamics.hamiltonianGradient,
    neg_one_smul, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg] using congrFun h x

private lemma euclideanEnvelope_zero {N p : ℕ} (hN : 0 < N) :
    euclideanEnvelope N p 1 0 = 0 := by
  let : NeZero N := ⟨hN.ne'⟩
  simp [euclideanEnvelope, pureJetEnvelope, unitJetEnvelope, absoluteSupremum]

private lemma tensorBallGradientSup_lipschitz {N p : ℕ}
    (hN : 0 < N) (hp : 1 ≤ p) :
    LipschitzWith (p : ℝ≥0)
      (fun g : EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p) =>
        tensorBallGradientSup (WithLp.ofLp g)) := by
  have henv : LipschitzWith (p : ℝ≥0) (euclideanEnvelope N p 1) := by
    simpa using euclideanEnvelope_lipschitz hN hp hp
  apply LipschitzWith.of_le_add_mul
  intro g z
  change sSup _ ≤ _
  refine csSup_le ⟨_, ⟨0, Metric.mem_closedBall_self (Real.sqrt_nonneg _), rfl⟩⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  have hz := le_csSup (tensorGradient_bddAbove hN (WithLp.ofLp z)) ⟨x, hx, rfl⟩
  have he := henv.dist_le_mul (g - z) 0
  rw [euclideanEnvelope_zero hN, dist_zero_right, dist_zero_right,
    Real.norm_eq_abs] at he
  change |pureJetEnvelope N p 1 (WithLp.ofLp (g - z))| ≤ (p : ℝ) * ‖g - z‖ at he
  rw [abs_of_nonneg (pureJetEnvelope_nonneg hN _)] at he
  have hd := gradient_norm_le_envelope hN (WithLp.ofLp (g - z)) x (by simpa using hx)
  rw [show WithLp.ofLp (g - z) = WithLp.ofLp g - WithLp.ofLp z from rfl,
    tensor_gradient_sub] at hd
  have hn := norm_sub_norm_le
    (gradient (SphericalAging.FiniteModel.Hamiltonian N p (WithLp.ofLp g)) x)
    (gradient (SphericalAging.FiniteModel.Hamiltonian N p (WithLp.ofLp z)) x)
  change _ ≤ tensorBallGradientSup (WithLp.ofLp z) + (p : ℝ) * dist g z
  rw [dist_eq_norm]
  change pureJetEnvelope N p 1 (WithLp.ofLp g - WithLp.ofLp z) ≤
    (p : ℝ) * ‖g - z‖ at he
  change ‖gradient (SphericalAging.FiniteModel.Hamiltonian N p (WithLp.ofLp z)) x‖ ≤
    tensorBallGradientSup (WithLp.ofLp z) at hz
  linarith

private lemma tensorBallGradientSup_continuous {N p : ℕ}
    (hN : 0 < N) (hp : 1 ≤ p) :
    Continuous (tensorBallGradientSup (N := N) (p := p)) := by
  exact (tensorBallGradientSup_lipschitz hN hp).continuous.comp
    (PiLp.continuous_toLp 2 _)

private def pureDegree (p : ℕ) (hp : 4 ≤ p) :
    Degree (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree :=
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
  ⟨⟨p, Nat.lt_succ_of_le (μ.degree_bounds (by simp [μ, FiniteMixture.pure])).2⟩,
    show 2 ≤ p by omega⟩

private lemma pure_field_eq {N : ℕ} (p : ℕ) (hp : 4 ≤ p)
    (J : Disorder N (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
    field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J =
      SphericalAging.FiniteModel.Hamiltonian N p (J (pureDegree p hp)) := by
  classical
  funext x
  unfold field
  rw [Finset.sum_eq_single (pureDegree p hp)]
  · simp [mixtureCoefficients, FiniteMixture.pure, blockField, pureDegree]
  · intro q _ hq
    have hqp : q.val.val ≠ p := by
      intro he
      apply hq
      apply Subtype.ext
      apply Fin.ext
      exact he
    simp [mixtureCoefficients, FiniteMixture.pure, hqp]
  · simp

private lemma ballGradientSup_pure_eq {N : ℕ} (p : ℕ) (hp : 4 ≤ p)
    (J : Disorder N (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
    ballGradientSup
      (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J =
        tensorBallGradientSup (J (pureDegree p hp)) := by
  unfold ballGradientSup tensorBallGradientSup
  rw [pure_field_eq p hp]
  rfl

/-- Manuscript `lem:pc-regularity`: the actual ball gradient supremum is
p-Lipschitz in the full Euclidean coordinates of the original disorder. -/
theorem pure_ballGradientSup_lipschitz (p : ℕ) (hp : 4 ≤ p)
    {N : ℕ} (hN : 2 ≤ N) :
    LipschitzWith (p : ℝ≥0)
      (fun g : EuclideanDisorder N
          (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree =>
        ballGradientSup
          (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity)))
          (unpackDisorder g)) := by
  let q := pureDegree p hp
  have hproj : LipschitzWith 1 (sourceDegreeProjectionCLM (N := N) q) :=
    (sourceDegreeProjectionCLM q).lipschitzWith.weaken (by
      exact_mod_cast sourceDegreeProjectionCLM_norm_le (N := N) q)
  have h := (tensorBallGradientSup_lipschitz (p := p) (by omega : 0 < N)
    (by omega : 1 ≤ p)).comp hproj
  simp only [mul_one, Function.comp_def] at h
  have heq (g : EuclideanDisorder N
      (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
      WithLp.ofLp (sourceDegreeProjectionCLM q g) = unpackDisorder g q := by
    rfl
  simpa only [heq, ballGradientSup_pure_eq p hp, q] using h

/-- Manuscript `lem:pc-regularity`: the original-disorder expected ball
gradient supremum is bounded by a constant depending only on p times sqrt N. -/
theorem pure_ballGradientSup_expected_bound (p : ℕ) (hp : 4 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable
        (ballGradientSup
          (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))))
        (disorderLaw N (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) ∧
      (∫ J, ballGradientSup
          (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J
        ∂disorderLaw N (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) ≤
          C * Real.sqrt (N : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  refine ⟨6 * (p : ℝ) * Real.sqrt p, by positivity, ?_⟩
  intro N hN
  have hN0 : 0 < N := by omega
  have hp1 : 1 ≤ p := by omega
  have hc := tensorBallGradientSup_continuous (p := p) hN0 hp1
  have hi : Integrable (tensorBallGradientSup (N := N) (p := p))
      (SphericalAging.FiniteModel.disorderLaw N p) :=
    (pureJetEnvelope_integrable (p := p) (j := 1) hN0).mono' hc.aestronglyMeasurable
      (.of_forall fun J => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tensorBallGradientSup_nonneg hN0 J)]
        exact tensorBallGradientSup_le_envelope hN0 J)
  have he := integral_mono hi (pureJetEnvelope_integrable (p := p) (j := 1) hN0)
    (tensorBallGradientSup_le_envelope hN0)
  have hb := expected_pureJetEnvelope_le (j := 1) hN0 hp1 hp1
  have hb' : (∫ J, tensorBallGradientSup J
      ∂SphericalAging.FiniteModel.disorderLaw N p) ≤
        6 * (p : ℝ) * Real.sqrt p * Real.sqrt (N : ℝ) := by
    exact he.trans (by norm_num [Real.sqrt_eq_rpow] at hb ⊢; exact hb)
  have hlaw := degree_block_hasLaw (N := N) (pureDegree p hp)
  constructor
  · simpa only [Function.comp_def, ← ballGradientSup_pure_eq p hp] using
      hlaw.integrable_comp hi
  · simpa only [Function.comp_def, ← ballGradientSup_pure_eq p hp] using
      (hlaw.integral_comp hi.aestronglyMeasurable).trans_le hb'

private lemma regularDisorder_ordered {N P : ℕ} (J : Disorder N P)
    (hJ : J ∈ regularDisorder) :
    J ∈ sourcePosteriorOrderedRegularity (∑ q : Degree P, blockThreshold q) := by
  intro q
  have hq : blockThreshold q ≤ ∑ r : Degree P, blockThreshold r :=
    Finset.single_le_sum (fun r _ => (blockThreshold_pos r).le) (Finset.mem_univ q)
  have hq0 : 0 ≤ (q.val.val : ℝ) := Nat.cast_nonneg _
  exact (hJ q).trans (by linarith)

/-- Manuscript `eq:pc-third`: the actual covariant spherical cubic operator
is uniformly O(1 / sqrt N) on the original `regularDisorder` event. -/
theorem pure_original_spherical_third_bound (p : ℕ) (hp : 4 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ (J : Disorder N (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree),
        J ∈ regularDisorder →
        ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
          ‖sourceSphereThirdExtension
            (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J x‖ ≤
              C / Real.sqrt (N : ℝ) := by
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
  let K := ∑ q : Degree μ.maxDegree, blockThreshold q
  have hK : 0 ≤ K := Finset.sum_nonneg (fun q _ => (blockThreshold_pos q).le)
  refine ⟨9 * sourcePosteriorDerivativeConstant (mixtureCoefficients μ) K,
    mul_pos (by norm_num) (sourcePosteriorDerivativeConstant_pos _ hK), ?_⟩
  intro N hN J hJ x hx
  exact (source_ordered_sphere_jet_bounds (by omega) (mixtureCoefficients μ) hK J
    (regularDisorder_ordered J hJ) x hx).2.2

end SlowEquilibration.PureHighEnergyRegularity
