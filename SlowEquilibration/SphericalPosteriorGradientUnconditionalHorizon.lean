-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPosteriorGradientExponentialHorizon
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail

/-! The physical center-gradient path bound no longer carries a regularity
indicator: the original tensor exceptional event has its separately proved
Gaussian landscape tail. -/
@[expose] public section
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem posteriorTrajectory_regularDisorder_failure_le
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) :
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1 ∉ regularDisorder} ≤
      Real.exp (-((n+1 : ℕ) : ℝ)) := by
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree) :=
    {z | unpackDisorder z ∉ regularDisorder}
  have hreg : MeasurableSet (regularDisorder (N := n+1)
      (P := μ.maxDegree))ᶜ := (regularDisorder_measurable _ _).compl
  have hu : Measurable (unpackDisorder (N := n+1) (P := μ.maxDegree)) := by
    unfold unpackDisorder
    fun_prop
  have hG : MeasurableSet G := hreg.preimage hu
  have hm : (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).real G =
      (disorderLaw (n+1) μ.maxDegree).real
        (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ := by
    change (stdGaussian (EuclideanSpace ℝ (Coordinate (n+1) μ.maxDegree))).real
      {ω | unpackDisorder ω ∉ regularDisorder} =
      (disorderLaw (n+1) μ.maxDegree).real {x | x ∉ regularDisorder}
    simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
      using (unpackDisorder_hasLaw (n+1) μ.maxDegree).measureReal_eq hreg
  have hfst : (posteriorTrajectoryLaw n μ).map Prod.fst =
      stdGaussian (EuclideanDisorder (n+1) μ.maxDegree) := by
    unfold posteriorTrajectoryLaw
    rw [Measure.map_fst_prod,measure_univ,one_smul]
  calc
    (posteriorTrajectoryLaw n μ).real
        {q | unpackDisorder q.1 ∉ regularDisorder} =
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).real G := by
        simp only [Measure.real]
        rw [← hfst,Measure.map_apply measurable_fst hG]
        rfl
    _ = (disorderLaw (n+1) μ.maxDegree).real
        (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ := hm
    _ ≤ _ := regularDisorder_failure_probability (by omega : 2 ≤ n+1)

/-- Full joint original Gaussian/uniform-start/Wiener path tail for the
mixed source center-gradient through an exponential horizon. -/
theorem mixedPosterior_gradient_exponential_horizon_tail
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (u : Vector (n+1)) (hu : ‖u‖ ^ 2 = (n+1 : ℕ))
    (e k β : ℝ) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α) (T : ℝ≥0) (hT : 0 < T)
    (hshort : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ) ≤
      α/(2*centerConstant μ Q))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hγ₁ : γ < α^2/(8*(Q*μ.xi1 Q)))
    (hγ₂ : γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) :
    let H := exponentialGridHorizon γ (n+1)
    (posteriorTrajectoryLaw n μ).real
      {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
        |mixedPosteriorOriginalGradientScore n μ Q u
          (scorePairEquiv (e,k)) β (H+2*T) t q|} ≤
      (2/(T:ℝ)+4) *
        (Real.exp (-((n+1 : ℕ) : ℝ)*
          (α^2/(8*(Q*μ.xi1 Q))-γ)) +
         Real.exp (-((n+1 : ℕ) : ℝ)*
          ((α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ))) +
      Real.exp (-((n+1 : ℕ) : ℝ)) := by
  dsimp only
  let H := exponentialGridHorizon γ (n+1)
  let A : Set (EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
      |mixedPosteriorOriginalGradientScore n μ Q u
        (scorePairEquiv (e,k)) β (H+2*T) t q|}
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | unpackDisorder q.1 ∈ regularDisorder}
  have hsub : A ⊆ (G ∩ A) ∪ Gᶜ := by
    intro q hq
    by_cases hg : q∈G
    · exact Or.inl ⟨hg,hq⟩
    · exact Or.inr hg
  have hGood := mixedPosterior_regular_gradient_exponential_horizon_tail
    n μ hnp Q hQ hQ1 u hu e k β hβ hα T hT hshort hγ hγ₁ hγ₂
  have hBad := posteriorTrajectory_regularDisorder_failure_le n hn μ
  have h := (measureReal_mono (μ := posteriorTrajectoryLaw n μ) hsub).trans
    (measureReal_union_le (G ∩ A) Gᶜ)
  have hh := h.trans (add_le_add hGood hBad)
  simpa only [A,G,H,Set.inter_def,Set.mem_ofPred_eq,
    Set.compl_ofPred] using hh

end SlowEquilibration.SphericalPosteriorGradientIndependence
