-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaExtension
public import SlowEquilibration.GaussianReplicaKernel

/-! Actual disorder derivatives of bounded Gibbs-replica observables.
The extra replica represents the derivative of the partition denominator.
Repeated derivatives are obtained by repeatedly applying this proved rule;
no replica differentiation identity is assumed.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianReplicaDerivatives

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianReplicaCalculus
open scoped Topology BigOperators NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V H : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- Every bounded replica observable has the literal covariance derivative. -/
theorem replicaExpectation_fderiv_covariance
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w d : H) :
    fderiv ℝ (replicaExpectation ν L n f) w d =
      replicaExpectation ν L n (fun σ => f σ * replicaLinear L n σ d) w -
      replicaExpectation ν L n f w *
        replicaExpectation ν L n (fun σ => replicaLinear L n σ d) w := by
  rw [(replicaExpectation_hasFDerivAt ν L hL hK hC hb n f hf hfb w).fderiv,
    expectationDerivative_apply (replicaBase ν n) f (replicaLinear L n) hf
      (replicaLinear_measurable L hL n) (hfb.and (replicaLinear_bound ν L hb n))]
  simp_rw [← replicaExpectation_eq_joint ν L hL hK hb]

/-- Differentiating an n-replica expectation adds one fresh independent
Gibbs replica to the denominator term. -/
theorem replicaExpectation_fderiv
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w d : H) :
    fderiv ℝ (replicaExpectation ν L n f) w d =
      (∑ a : Fin n, replicaExpectation ν L n (fun σ => f σ * L (σ a) d) w) -
      (n : ℝ) * replicaExpectation ν L (n+1)
        (fun σ => f (initialReplicas σ) * L (σ (Fin.last n)) d) w := by
  have hcoord (a : Fin n) :
      ∀ᵐ σ ∂replicaBase ν n, ‖L (σ a)‖ ≤ K :=
    (measurePreserving_eval (μ := fun _ : Fin n => ν) a).quasiMeasurePreserving.ae hb
  have hbound (a : Fin n) : ∀ᵐ σ ∂replicaBase ν n,
      |f σ * L (σ a) d| ≤ C * (K * ‖d‖) := by
    filter_upwards [hfb, hcoord a] with σ hσ hLa
    rw [abs_mul]
    exact mul_le_mul hσ ((L (σ a)).le_opNorm d |>.trans
      (mul_le_mul_of_nonneg_right hLa (norm_nonneg d))) (abs_nonneg _) hC
  have hsum := replicaExpectation_finiteSum ν L hL hK hb n
    (fun a σ => f σ * L (σ a) d)
    (fun a => hf.mul (((ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL).comp
      (measurable_pi_apply a))) hbound w
  rw [replicaExpectation_fderiv_covariance ν L hL hK hC hb n f hf hfb,
    replicaExpectation_linear_apply ν L hL hb]
  have hfirst : replicaExpectation ν L n (fun σ => f σ * replicaLinear L n σ d) w =
      ∑ a : Fin n, replicaExpectation ν L n (fun σ => f σ * L (σ a) d) w := by
    simpa only [replicaLinear, sum_apply, Finset.mul_sum] using hsum
  rw [hfirst, replicaExpectation_append ν L hL hb n w f (fun z => L z d)]
  ring

/-- One fresh-replica observable contains the entire derivative rule. -/
def derivativeObservable (L : V → H →L[ℝ] ℝ) {n : ℕ}
    (f : (Fin n → V) → ℝ) (d : H) (σ : Fin (n+1) → V) : ℝ :=
  f (initialReplicas σ) *
    (replicaLinear L n (initialReplicas σ) d - (n : ℝ) * L (σ (Fin.last n)) d)

theorem derivativeObservable_measurable (L : V → H →L[ℝ] ℝ) (hL : Measurable L)
    {n : ℕ} (f : (Fin n → V) → ℝ) (hf : Measurable f) (d : H) :
    Measurable (derivativeObservable L f d) :=
  (hf.comp (initialReplicas_measurable n)).mul
    ((((ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp
      (replicaLinear_measurable L hL n)).comp (initialReplicas_measurable n)).sub
      ((((ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL).comp
        (measurable_pi_apply (Fin.last n))).const_mul (n : ℝ)))

theorem derivativeObservable_bound (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) {K C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) {n : ℕ} (f : (Fin n → V) → ℝ)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (d : H) :
    ∀ᵐ σ ∂replicaBase ν (n+1),
      |derivativeObservable L f d σ| ≤ C * (2 * (n : ℝ) * K * ‖d‖) := by
  have hprefix : ∀ᵐ σ ∂replicaBase ν (n+1), |f (initialReplicas σ)| ≤ C :=
    ((GaussianReplicaKernel.initial_pi_hasLaw ν n).measurePreserving
      (GaussianReplicaKernel.initial_measurable n)).quasiMeasurePreserving.ae hfb
  have hlinear : ∀ᵐ σ ∂replicaBase ν (n+1),
      ‖replicaLinear L n (initialReplicas σ)‖ ≤ (n : ℝ) * K :=
    ((GaussianReplicaKernel.initial_pi_hasLaw ν n).measurePreserving
      (GaussianReplicaKernel.initial_measurable n)).quasiMeasurePreserving.ae
      (replicaLinear_bound ν L hb n)
  have hlast : ∀ᵐ σ ∂replicaBase ν (n+1), ‖L (σ (Fin.last n))‖ ≤ K :=
    (measurePreserving_eval (μ := fun _ : Fin (n+1) => ν)
      (Fin.last n)).quasiMeasurePreserving.ae hb
  filter_upwards [hprefix, hlinear, hlast] with σ hp hl hz
  rw [derivativeObservable, abs_mul]
  apply mul_le_mul hp _ (abs_nonneg _) hC
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h₁ := (replicaLinear L n (initialReplicas σ)).le_opNorm d |>.trans
    (mul_le_mul_of_nonneg_right hl (norm_nonneg d))
  have h₂ := (L (σ (Fin.last n))).le_opNorm d |>.trans
    (mul_le_mul_of_nonneg_right hz (norm_nonneg d))
  simp only [Real.norm_eq_abs] at h₁ h₂
  nlinarith [mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The covariance rule as one actual (n+1)-replica integral. -/
theorem replicaExpectation_fderiv_eq_next
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w d : H) :
    fderiv ℝ (replicaExpectation ν L n f) w d =
      replicaExpectation ν L (n+1) (derivativeObservable L f d) w := by
  let G := gibbsMeasure ν L w
  let _ := gibbsMeasure_probability ν L hL hb w
  have hlinear : Measurable (fun σ : Fin n → V => replicaLinear L n σ d) :=
    (ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp
      (replicaLinear_measurable L hL n)
  have hbound : ∀ᵐ σ ∂replicaBase ν n,
      |f σ * replicaLinear L n σ d| ≤ C * ((n : ℝ) * K * ‖d‖) := by
    filter_upwards [hfb, replicaLinear_bound ν L hb n] with σ hσ hl
    rw [abs_mul]
    exact mul_le_mul hσ ((replicaLinear L n σ).le_opNorm d |>.trans
      (mul_le_mul_of_nonneg_right hl (norm_nonneg d))) (abs_nonneg _) hC
  have hi₁ := replicaObservable_integrable ν L hL hK hb n _ (hf.mul hlinear) hbound w
  have hi₁' : Integrable (fun σ : Fin (n+1) → V =>
      f (initialReplicas σ) * replicaLinear L n (initialReplicas σ) d)
      (Measure.pi (fun _ : Fin (n+1) => G)) :=
    (GaussianReplicaKernel.initial_pi_hasLaw G n).integrable_comp hi₁
  have hfl : Measurable (fun σ : Fin (n+1) → V =>
      f (initialReplicas σ) * L (σ (Fin.last n)) d) :=
    (hf.comp (initialReplicas_measurable n)).mul
      (((ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL).comp
        (measurable_pi_apply (Fin.last n)))
  have hflb : ∀ᵐ σ ∂replicaBase ν (n+1),
      |f (initialReplicas σ) * L (σ (Fin.last n)) d| ≤ C * (K * ‖d‖) := by
    have hp := ((GaussianReplicaKernel.initial_pi_hasLaw ν n).measurePreserving
      (GaussianReplicaKernel.initial_measurable n)).quasiMeasurePreserving.ae hfb
    have hz := (measurePreserving_eval (μ := fun _ : Fin (n+1) => ν)
      (Fin.last n)).quasiMeasurePreserving.ae hb
    filter_upwards [hp, hz] with σ hσ hl
    rw [abs_mul]
    exact mul_le_mul hσ ((L (σ (Fin.last n))).le_opNorm d |>.trans
      (mul_le_mul_of_nonneg_right hl (norm_nonneg d))) (abs_nonneg _) hC
  have hi₂ := replicaObservable_integrable ν L hL hK hb (n+1) _ hfl hflb w
  have hprefix : replicaExpectation ν L (n+1)
      (fun σ => f (initialReplicas σ) * replicaLinear L n (initialReplicas σ) d) w =
      replicaExpectation ν L n (fun σ => f σ * replicaLinear L n σ d) w := by
    have hh := replicaExpectation_append ν L hL hb n w
      (fun σ => f σ * replicaLinear L n σ d) (fun _ => (1 : ℝ))
    simpa only [mul_one, expectation, div_self (moment_one_pos ν L hL hb w).ne'] using hh
  rw [replicaExpectation_fderiv_covariance ν L hL hK hC hb n f hf hfb,
    replicaExpectation_linear_apply ν L hL hb]
  have hrhs : replicaExpectation ν L (n+1) (derivativeObservable L f d) w =
      replicaExpectation ν L n (fun σ => f σ * replicaLinear L n σ d) w -
      (n : ℝ) * replicaExpectation ν L (n+1)
        (fun σ => f (initialReplicas σ) * L (σ (Fin.last n)) d) w := by
    have hsplit : derivativeObservable L f d = fun σ =>
        f (initialReplicas σ) * replicaLinear L n (initialReplicas σ) d -
          (n : ℝ) * (f (initialReplicas σ) * L (σ (Fin.last n)) d) := by
      funext σ
      unfold derivativeObservable
      ring
    rw [hsplit, replicaExpectation, integral_sub hi₁' (hi₂.const_mul (n : ℝ)),
      integral_const_mul]
    exact congrArg (fun z => z - (n : ℝ) * replicaExpectation ν L (n+1)
      (fun σ => f (initialReplicas σ) * L (σ (Fin.last n)) d) w) hprefix
  rw [hrhs, replicaExpectation_append ν L hL hb n w f (fun z => L z d)]
  ring

/-- Repeated directional derivatives, with the final direction applied last.
The definition uses genuine Fréchet derivatives at every order. -/
def directionalDerivatives (f : H → ℝ) : (n : ℕ) → (Fin n → H) → H → ℝ
  | 0, _ => f
  | n+1, d => fun w => fderiv ℝ
      (directionalDerivatives f n (fun i => d i.castSucc)) w (d (Fin.last n))

/-- The replicated polynomial observable for the (n+1)st derivative of
log Z. Every differentiation appends exactly one replica. -/
def logReplicaObservable (L : V → H →L[ℝ] ℝ) :
    (n : ℕ) → (Fin (n+1) → H) → (Fin (n+1) → V) → ℝ
  | 0, d, σ => L (σ 0) (d 0)
  | n+1, d, σ => derivativeObservable L
      (logReplicaObservable L n (fun i => d i.castSucc)) (d (Fin.last (n+1))) σ

theorem logReplicaObservable_measurable (L : V → H →L[ℝ] ℝ) (hL : Measurable L)
    (n : ℕ) (d : Fin (n+1) → H) : Measurable (logReplicaObservable L n d) := by
  induction n with
  | zero =>
      exact ((ContinuousLinearMap.apply ℝ ℝ (d 0)).continuous.measurable.comp hL).comp
        (measurable_pi_apply 0)
  | succ n ih =>
      exact derivativeObservable_measurable L hL _ (ih _) _

/-- All repeated-derivative observables have an actual deterministic bound
under the product base measure. The constant may depend on the directions
and derivative order, but not on the disorder. -/
theorem logReplicaObservable_bounded (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (d : Fin (n+1) → H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ σ ∂replicaBase ν (n+1),
      |logReplicaObservable L n d σ| ≤ C := by
  induction n with
  | zero =>
      refine ⟨K * ‖d 0‖, by positivity, ?_⟩
      have hh := (measurePreserving_eval (μ := fun _ : Fin 1 => ν)
        (0 : Fin 1)).quasiMeasurePreserving.ae hb
      filter_upwards [hh] with σ hσ
      exact (L (σ 0)).le_opNorm (d 0) |>.trans
        (mul_le_mul_of_nonneg_right hσ (norm_nonneg _))
  | succ n ih =>
      obtain ⟨C, hC, hbC⟩ := ih (fun i => d i.castSucc)
      refine ⟨C * (2 * ((n+1 : ℕ) : ℝ) * K * ‖d (Fin.last (n+1))‖),
        by positivity, ?_⟩
      exact derivativeObservable_bound ν L hC hb _ hbC _

/-- The actual kth log-partition derivative is the expectation of the
recursively differentiated Gibbs observable, for every order and direction.
Only bounded measurable features are needed; no thermodynamic hypothesis
or replica identity is an argument of this theorem. -/
theorem directionalDerivatives_logPartition
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin (n+1) → H) (w : H) :
    directionalDerivatives (logPartition ν L) (n+1) d w =
      replicaExpectation ν L (n+1) (logReplicaObservable L n d) w := by
  induction n generalizing w with
  | zero =>
      change fderiv ℝ (logPartition ν L) w (d 0) = _
      rw [(logPartition_hasFDerivAt ν L hL hK hb w).fderiv, score_apply ν L hL hb]
      exact (replicaExpectation_coordinate ν L hL hb 1 (0 : Fin 1) w
        (fun v => L v (d 0))
        ((ContinuousLinearMap.apply ℝ ℝ (d 0)).continuous.measurable.comp hL)).symm
  | succ n ih =>
      have heq : directionalDerivatives (logPartition ν L) (n+1)
          (fun i => d i.castSucc) =
          replicaExpectation ν L (n+1)
            (logReplicaObservable L n (fun i => d i.castSucc)) := by
        funext z
        exact ih _ z
      change fderiv ℝ (directionalDerivatives (logPartition ν L) (n+1)
        (fun i => d i.castSucc)) w (d (Fin.last (n+1))) = _
      rw [heq]
      obtain ⟨C, hC, hbC⟩ := logReplicaObservable_bounded ν L hK hb n
        (fun i => d i.castSucc)
      exact replicaExpectation_fderiv_eq_next ν L hL hK hC hb (n+1) _
        (logReplicaObservable_measurable L hL n _) hbC w _

/-- A finite set of histories for the (n+1)st derivative. At each step,
the newly differentiated feature chooses one old replica or the fresh one. -/
def ExpansionIndex : ℕ → Type
  | 0 => Unit
  | n+1 => ExpansionIndex n × Fin (n+2)

instance expansionIndex_fintype : (n : ℕ) → Fintype (ExpansionIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd (ExpansionIndex n) (Fin (n+2))
      (expansionIndex_fintype n) inferInstance

/-- The signed multiplicity of a derivative history. -/
def expansionCoefficient : (n : ℕ) → ExpansionIndex n → ℝ
  | 0, _ => 1
  | n+1, t => expansionCoefficient n t.1 *
      (if t.2 = Fin.last (n+1) then -((n+1 : ℕ) : ℝ) else 1)

/-- Which Gibbs replica supplies each differentiated feature. -/
def expansionLabels : (n : ℕ) → ExpansionIndex n → Fin (n+1) → Fin (n+1)
  | 0, _ => fun _ => 0
  | n+1, t => Fin.snoc (fun j => (expansionLabels n t.1 j).castSucc) t.2

/-- Every derivative term contains each direction exactly once. -/
def featureMonomial (L : V → H →L[ℝ] ℝ) {r k : ℕ}
    (labels : Fin k → Fin r) (d : Fin k → H) (σ : Fin r → V) : ℝ :=
  ∏ j, L (σ (labels j)) (d j)

theorem featureMonomial_measurable (L : V → H →L[ℝ] ℝ) (hL : Measurable L)
    {r k : ℕ} (labels : Fin k → Fin r) (d : Fin k → H) :
    Measurable (featureMonomial L labels d) := by
  unfold featureMonomial
  exact Finset.measurable_prod _ fun j _ =>
    ((ContinuousLinearMap.apply ℝ ℝ (d j)).continuous.measurable.comp hL).comp
      (measurable_pi_apply (labels j))

theorem featureMonomial_bound (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) {K : ℝ} (_hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) {r k : ℕ}
    (labels : Fin k → Fin r) (d : Fin k → H) :
    ∀ᵐ σ ∂replicaBase ν r,
      |featureMonomial L labels d σ| ≤ ∏ j, K * ‖d j‖ := by
  have hall : ∀ᵐ σ ∂replicaBase ν r, ∀ j : Fin k, ‖L (σ (labels j))‖ ≤ K := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (μ := fun _ : Fin r => ν)
      (labels j)).quasiMeasurePreserving.ae hb
  filter_upwards [hall] with σ hσ
  rw [featureMonomial, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ =>
    (L (σ (labels j))).le_opNorm (d j) |>.trans
      (mul_le_mul_of_nonneg_right (hσ j) (norm_nonneg _))

private theorem derivative_choice_sum (L : V → H →L[ℝ] ℝ) (r : ℕ)
    (σ : Fin (r+1) → V) (d : H) :
    (∑ a : Fin (r+1),
      (if a = Fin.last r then -(r : ℝ) else 1) * L (σ a) d) =
      replicaLinear L r (initialReplicas σ) d - (r : ℝ) * L (σ (Fin.last r)) d := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte, one_mul, neg_mul,
    replicaLinear, sum_apply, initialReplicas]
  ring

/-- Closed finite expansion of every derivative observable. The coefficients
and replica labels depend only on the order, not on the model, dimension,
directions, disorder or temperature. -/
theorem logReplicaObservable_expansion (L : V → H →L[ℝ] ℝ)
    (n : ℕ) (d : Fin (n+1) → H) (σ : Fin (n+1) → V) :
    logReplicaObservable L n d σ =
      ∑ t : ExpansionIndex n, expansionCoefficient n t *
        featureMonomial L (expansionLabels n t) d σ := by
  induction n with
  | zero => simp [logReplicaObservable, ExpansionIndex, expansionCoefficient,
      featureMonomial, expansionLabels]
  | succ n ih =>
      change derivativeObservable L _ _ σ = _
      rw [derivativeObservable, ih, ← derivative_choice_sum L (n+1) σ]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      change _ = ∑ t : ExpansionIndex n × Fin (n+2),
        expansionCoefficient (n+1) t * featureMonomial L (expansionLabels (n+1) t) d σ
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro a _
      simp only [expansionCoefficient, featureMonomial]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [expansionLabels, Fin.snoc_castSucc, Fin.snoc_last, initialReplicas]
      ring

/-- The kth actual disorder derivative of log Z is a finite linear
combination of replicated feature monomials, with exactly k factors.
This is the form used for the independent-copy tensor contraction. -/
theorem directionalDerivatives_logPartition_expansion
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin (n+1) → H) (w : H) :
    directionalDerivatives (logPartition ν L) (n+1) d w =
      ∑ t : ExpansionIndex n, expansionCoefficient n t *
        replicaExpectation ν L (n+1)
          (featureMonomial L (expansionLabels n t) d) w := by
  rw [directionalDerivatives_logPartition ν L hL hK hb]
  have heq : logReplicaObservable L n d = fun σ =>
      ∑ t : ExpansionIndex n, expansionCoefficient n t *
        featureMonomial L (expansionLabels n t) d σ :=
    funext (logReplicaObservable_expansion L n d)
  rw [heq, replicaExpectation, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    exact integral_const_mul _ _
  · intro t _
    exact (replicaObservable_integrable ν L hL hK hb (n+1) _
      (featureMonomial_measurable L hL _ _) (featureMonomial_bound ν L hK hb _ _) w).const_mul _

/-- A deterministic operator bound for the derivative of every bounded
replica expectation. -/
theorem replicaExpectation_fderiv_norm_le
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w : H) :
    ‖fderiv ℝ (replicaExpectation ν L n f) w‖ ≤ 2 * C * ((n : ℝ) * K) := by
  rw [(replicaExpectation_hasFDerivAt ν L hL hK hC hb n f hf hfb w).fderiv]
  exact norm_expectationDerivative_le (replicaBase ν n) f (replicaLinear L n) hf
    (replicaLinear_measurable L hL n) hC (mul_nonneg (Nat.cast_nonneg n) hK)
    (hfb.and (replicaLinear_bound ν L hb n)) w

theorem replicaExpectation_lipschitz
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) :
    LipschitzWith (2 * C * ((n : ℝ) * K)).toNNReal (replicaExpectation ν L n f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((replicaExpectation_contDiff ν L hL hK hC hb n f hf hfb).differentiable (by norm_num))
  intro w
  apply (NNReal.coe_le_coe).mp
  change ‖fderiv ℝ (replicaExpectation ν L n f) w‖ ≤ _
  rw [Real.coe_toNNReal _ (by positivity)]
  exact replicaExpectation_fderiv_norm_le ν L hL hK hC hb n f hf hfb w

/-- Every repeated directional derivative of log Z is continuously
differentiable, including the order-zero log partition itself. -/
theorem directionalDerivatives_logPartition_contDiff
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin n → H) :
    ContDiff ℝ 1 (directionalDerivatives (logPartition ν L) n d) := by
  cases n with
  | zero => exact logPartition_contDiff ν L hL hK hb
  | succ n =>
      have heq : directionalDerivatives (logPartition ν L) (n+1) d =
          replicaExpectation ν L (n+1) (logReplicaObservable L n d) :=
        funext (directionalDerivatives_logPartition ν L hL hK hb n d)
      rw [heq]
      obtain ⟨C, hC, hbC⟩ := logReplicaObservable_bounded ν L hK hb n d
      exact replicaExpectation_contDiff ν L hL hK hC hb (n+1) _
        (logReplicaObservable_measurable L hL n d) hbC

/-- The positive-order derivatives have a deterministic global bound. -/
theorem directionalDerivatives_logPartition_bounded
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin (n+1) → H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, |directionalDerivatives (logPartition ν L) (n+1) d w| ≤ C := by
  obtain ⟨C, hC, hbC⟩ := logReplicaObservable_bounded ν L hK hb n d
  refine ⟨C, hC, fun w => ?_⟩
  rw [directionalDerivatives_logPartition ν L hL hK hb]
  exact norm_replicaExpectation_le ν L hL hK hC hb (n+1) _
    (logReplicaObservable_measurable L hL n d) hbC w

/-- All repeated directional derivatives of log Z are globally Lipschitz.
The constant may depend on order and directions; it is independent of w. -/
theorem directionalDerivatives_logPartition_lipschitz
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (d : Fin n → H) :
    ∃ B : ℝ≥0, LipschitzWith B (directionalDerivatives (logPartition ν L) n d) := by
  cases n with
  | zero =>
      refine ⟨K.toNNReal, ?_⟩
      apply lipschitzWith_of_nnnorm_fderiv_le
        ((logPartition_contDiff ν L hL hK hb).differentiable (by norm_num))
      intro w
      apply (NNReal.coe_le_coe).mp
      change ‖fderiv ℝ (logPartition ν L) w‖ ≤ _
      rw [(logPartition_hasFDerivAt ν L hL hK hb w).fderiv, Real.coe_toNNReal K hK]
      exact norm_score_le ν L hL hK hb w
  | succ n =>
      have heq : directionalDerivatives (logPartition ν L) (n+1) d =
          replicaExpectation ν L (n+1) (logReplicaObservable L n d) :=
        funext (directionalDerivatives_logPartition ν L hL hK hb n d)
      rw [heq]
      obtain ⟨C, hC, hbC⟩ := logReplicaObservable_bounded ν L hK hb n d
      exact ⟨_, replicaExpectation_lipschitz ν L hL hK hC hb (n+1) _
        (logReplicaObservable_measurable L hL n d) hbC⟩

end SlowEquilibration.GaussianReplicaDerivatives
