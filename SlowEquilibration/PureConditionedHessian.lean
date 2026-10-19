-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ValueTangentConditioning

/-! # Proper pure-model whole-field Hessian conditioning

The canonical pure coefficient sequence is used literally. Euler's identity
proves K=pH for the same disorder. Conditioning observes value and the complete
tangent gradient, omitting the redundant radial coordinate, and yields the
actual full intrinsic GOE Hessian shifted by p times the normalized value.
-/

@[expose] public section

namespace SlowEquilibration.PureConditionedHessian

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.ConditionedIntrinsicHessian
open SlowEquilibration.ValueTangentConditioning SlowEquilibration.SphericalForm
open SlowEquilibration.SphereHessian
open scoped RealInnerProductSpace ENNReal Topology BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Actual Euler identity for every coefficient sequence supported in one degree. -/
theorem radial_jet_of_single_degree {N P : ℕ} (p : ℕ) (c : Degree P → ℝ)
    (hc : ∀ q, q.val.val ≠ p → c q = 0) (J : Disorder N P) (x : Vector N) :
    jet c 1 x (fun _ => x) J = (p : ℝ) * jet c 0 x (fun i => Fin.elim0 i) J := by
  rw [radial_jet_sum, jet, iteratedFDeriv_zero_apply, field, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqp : q.val.val = p
  · rw [hqp]
    ring
  · rw [hc q hqp]
    simp

/-- The actual centered canonical pure model has exactly the source relation K=pH. -/
theorem pure_radial_jet {N : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp alpha halpha).maxDegree) (x : Vector N) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
    jet c 1 x (fun _ => x) J = (p : ℝ) * jet c 0 x (fun i => Fin.elim0 i) J := by
  dsimp only
  apply radial_jet_of_single_degree
  intro q hqp
  simp [centerCoefficients, mixtureCoefficients, FiniteMixture.pure, hqp]

/-- Full true ambient GOE Hessian law under the proper value/tangent target,
for any actual finite mixture, including pure models. -/
theorem valueTangent_conditioned_ambient_hasLaw {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0)
    (a : EuclideanSpace ℝ (Sum (Fin 1) (Fin k))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (hessianMatrix c x e) (goeLaw k N (Q ^ 2 * μ.xi2 Q))
      (coefficientKernel (valueTangentCLM c x e) a) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm : Measurable (actualObservation (ambientHessianCLM c x e)) :=
    (ambientHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N μ.maxDegree => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N μ.maxDegree))
  have hH : Measurable (hessianMatrix c x e) := by
    convert (hessianDecode_measurable k).comp hm using 1
    funext J
    exact (hessianDecode_actual c x e J).symm
  refine ⟨hH.aemeasurable, ?_⟩
  rw [valueTangent_ambientHessian_map c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ) x e htan]
  exact (center_hessian_matrix_hasLaw hN μ hQ x hx e he htan).map_eq

/-- Proper pure whole-field conditioning at every value/tangent-gradient
null target gives the true full intrinsic shifted GOE Hessian. -/
theorem pure_conditioned_intrinsicMatrix_hasLaw {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ))
    (a : EuclideanSpace ℝ (Sum (Fin 1) (Fin n))) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (intrinsicMatrix c x hx)
      ((goeLaw n (n + 1) (Q ^ 2 * μ.xi2 Q)).map
        (fun W => W - ((p : ℝ) * a (Sum.inl 0) / (n + 1 : ℕ)) •
          (1 : Matrix (Fin n) (Fin n) ℝ)))
      (coefficientKernel (valueTangentCLM c x (tangentFrame x hx)) a) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hH := valueTangent_conditioned_ambient_hasLaw (by omega) μ hQ.le x hx
    (tangentFrame x hx) (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) a
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      W - ((p : ℝ) * a (Sum.inl 0) / (n + 1 : ℕ)) • 1) := by fun_prop
  have hshift := (hasLaw_map hm.aemeasurable).fun_comp hH
  apply hshift.congr
  filter_upwards [coefficientKernel_observation_ae _
    (center_valueTangent_surjective (by omega) μ hQ x hx (tangentFrame x hx)
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)) a] with J hJ
  have hv := congrArg (fun y : EuclideanSpace ℝ (Sum (Fin 1) (Fin n)) => y (Sum.inl 0)) hJ
  change valueTangentCLM c x (tangentFrame x hx) (euclideanDisorder J) (Sum.inl 0) = a (Sum.inl 0) at hv
  rw [valueTangentCLM_apply_value, unpack_euclideanDisorder] at hv
  change intrinsicMatrix c x hx J = _
  rw [intrinsicMatrix, intrinsicHessian_toMatrix c J x hx, radialMultiplier_eq_jet,
    pure_radial_jet p hp alpha halpha Q J x, hv]

/-- A literal normalized-value target with all true tangent coordinates zero. -/
def valueTarget (n : ℕ) (h : ℝ) : EuclideanSpace ℝ (Sum (Fin 1) (Fin n)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sum (Fin 1) (Fin n) => ℝ)).symm
    (Sum.elim (fun _ => (n + 1 : ℕ) * h) (fun _ => 0))

/-- At the manuscript pure target H=Nh, the intrinsic identity shift is ph. -/
theorem pure_hessian_at_normalized_value {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (intrinsicMatrix c x hx)
      ((goeLaw n (n + 1) (Q ^ 2 * μ.xi2 Q)).map
        (fun W => W - ((p : ℝ) * h) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (coefficientKernel (valueTangentCLM c x (tangentFrame x hx)) (valueTarget n h)) := by
  have he : (p : ℝ) * valueTarget n h (Sum.inl 0) / (n + 1 : ℕ) = (p : ℝ) * h := by
    change (p : ℝ) * ((n + 1 : ℕ) * h) / (n + 1 : ℕ) = _
    have hN : (n + 1 : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
  simpa only [he] using pure_conditioned_intrinsicMatrix_hasLaw p hp alpha halpha hQ x hx (valueTarget n h)

/-- Proper value/tangent conditioning with zero tangent target is supported
on the actual critical point, without redundant radial conditioning. -/
theorem valueTangent_conditioned_critical_ae {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) (h : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂coefficientKernel (valueTangentCLM c x (tangentFrame x hx)) (valueTarget n h),
      surfaceGradient (field c J) x = 0 := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  filter_upwards [coefficientKernel_observation_ae _
    (center_valueTangent_surjective (by omega) μ hQ x hx (tangentFrame x hx)
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)) (valueTarget n h)] with J hJ
  have hzero : intrinsicGamma c x (euclideanDisorder J) = 0 := by
    apply (tangentBasis x hx).repr.injective
    apply PiLp.ext
    intro i
    rw [OrthonormalBasis.repr_apply_apply, map_zero]
    change inner ℝ (tangentBasis x hx i) (intrinsicGamma c x (euclideanDisorder J)) = 0
    rw [intrinsicGamma_inner, unpack_euclideanDisorder]
    have h := congrArg (fun y : EuclideanSpace ℝ (Sum (Fin 1) (Fin n)) => y (Sum.inr i)) hJ
    change valueTangentCLM c x (tangentFrame x hx) (euclideanDisorder J) (Sum.inr i) = 0 at h
    rw [valueTangentCLM_apply_gradient, unpack_euclideanDisorder] at h
    exact h
  have he := congrArg (fun v : tangentPlane x => (v : Vector (n + 1))) hzero
  simpa only [intrinsicGamma_coe (by omega) c x hx, unpack_euclideanDisorder, Submodule.coe_zero] using he

end
end SlowEquilibration.PureConditionedHessian
