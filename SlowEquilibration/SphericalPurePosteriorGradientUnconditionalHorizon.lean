-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPurePosteriorGradientExponentialHorizon
public import SlowEquilibration.SphericalPosteriorGradientUnconditionalHorizon
public import SlowEquilibration.SourcePhysicalPairPhysicalPosteriorRegularity

/-! Unconditional exponential-horizon estimate for the actual proper
value/zero-gradient posterior. Both tensor exceptional probabilities are
proved under their correct original-Gaussian and value-posterior laws. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalOverlapExponential SphericalMarkedWindows
open ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- The actual original-Gaussian value-posterior map has the coefficient
kernel law, so source posterior tensor regularity transfers to the joint
trajectory law without a supplied exceptional-event hypothesis. -/
theorem valuePosterior_posteriorRegularity_failure_le
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e K : ℝ)
    (hKernel : (valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu e).real
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ ≤
      (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2)) :
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder (valuePosterior n μ Q u e q.1) ∉
        sourcePosteriorOrderedRegularity K} ≤
      (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) := by
  let F : EuclideanDisorder (n+1) μ.maxDegree → Disorder (n+1) μ.maxDegree :=
    fun z => unpackDisorder (valuePosterior n μ Q u e z)
  let B : Set (Disorder (n+1) μ.maxDegree) :=
    (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ
  have hB : MeasurableSet B :=
    (sourcePosteriorOrderedRegularity_measurable (n+1) μ.maxDegree K).compl
  have hp : Measurable (valuePosterior n μ Q u e) := by
    exact ((valuePosterior_continuous n μ Q).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)).measurable
  have hF : Measurable F := by
    unfold F unpackDisorder
    exact (WholeFieldRegression.unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp
  have hfst : (posteriorTrajectoryLaw n μ).map Prod.fst =
      stdGaussian (EuclideanDisorder (n+1) μ.maxDegree) := by
    unfold posteriorTrajectoryLaw
    rw [Measure.map_fst_prod,measure_univ,one_smul]
  calc
    (posteriorTrajectoryLaw n μ).real {q | F q.1 ∈ B} =
        (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).real {z | F z ∈ B} := by
      simp only [Measure.real]
      rw [← hfst]
      change ((posteriorTrajectoryLaw n μ) {q | F q.1 ∈ B}).toReal =
        (((posteriorTrajectoryLaw n μ).map Prod.fst) (F ⁻¹' B)).toReal
      rw [Measure.map_apply measurable_fst (hB.preimage hF)]
      rfl
    _ = (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu e).real B := by
      have hmap : valueConditionedLaw
          (centerCoefficients (mixtureCoefficients μ) Q) u hu e =
          (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map F := by
        unfold F unpackDisorder
        exact valueConditionedLaw_eq_map n μ hQ u hu e
      rw [hmap,map_measureReal_apply hF hB]
      rfl
    _ ≤ _ := hKernel

theorem valuePosterior_gradient_exponential_horizon_tail
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (Q : ℝ) (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e β : ℝ) (hβ : 0 ≤ β)
    (K : ℝ) (hK : 0 ≤ K)
    (hKernel : (valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu e).real
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ ≤
      (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2))
    {α : ℝ} (hα : 0 < α) (T : ℝ≥0) (hT : 0 < T)
    (hshort : 4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
      α/(2*centerConstant μ Q))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hγ₁ : γ < α^2/(8*(Q*μ.xi1 Q)))
    (hγ₂ : γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) :
    let H := exponentialGridHorizon γ (n+1)
    (posteriorTrajectoryLaw n μ).real
      {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
        |valuePosteriorOriginalGradientScore n μ Q u e β (H+2*T) t q|} ≤
      (2/(T:ℝ)+4) *
        (Real.exp (-((n+1:ℕ):ℝ)*(α^2/(8*(Q*μ.xi1 Q))-γ)) +
         Real.exp (-((n+1:ℕ):ℝ)*
           ((α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ))) +
      Real.exp (-((n+1:ℕ):ℝ)) +
      (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) := by
  dsimp only
  let H := exponentialGridHorizon γ (n+1)
  let A : Set (EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
      |valuePosteriorOriginalGradientScore n μ Q u e β (H+2*T) t q|}
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | unpackDisorder q.1 ∈ regularDisorder ∧
      unpackDisorder (valuePosterior n μ Q u e q.1) ∈ sourcePosteriorOrderedRegularity K}
  let O : Set (EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | unpackDisorder q.1 ∉ regularDisorder}
  let P : Set (EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | unpackDisorder (valuePosterior n μ Q u e q.1) ∉ sourcePosteriorOrderedRegularity K}
  have hsub : A ⊆ (G ∩ A) ∪ (O ∪ P) := by
    intro q hq
    by_cases hO : q ∈ O
    · exact Or.inr (Or.inl hO)
    by_cases hP : q ∈ P
    · exact Or.inr (Or.inr hP)
    · exact Or.inl ⟨⟨not_not.mp hO,not_not.mp hP⟩,hq⟩
  have hGood := valuePosterior_regular_gradient_exponential_horizon_tail
    n μ Q hQ u hu e β hβ K hK hα T hT hshort hγ hγ₁ hγ₂
  have hGood' : (posteriorTrajectoryLaw n μ).real (G ∩ A) ≤
      (2/(T:ℝ)+4) *
        (Real.exp (-((n+1:ℕ):ℝ)*(α^2/(8*(Q*μ.xi1 Q))-γ)) +
         Real.exp (-((n+1:ℕ):ℝ)*
           ((α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ))) := by
    simpa only [G,A,H,Set.inter_def,Set.mem_ofPred_eq,and_assoc] using hGood
  have hOriginal := posteriorTrajectory_regularDisorder_failure_le n hn μ
  have hPosterior := valuePosterior_posteriorRegularity_failure_le
    n μ Q hQ u hu e K hKernel
  have h := (measureReal_mono (μ := posteriorTrajectoryLaw n μ) hsub).trans
    (measureReal_union_le (G ∩ A) (O ∪ P))
  have hh := h.trans (add_le_add hGood'
    ((measureReal_union_le O P).trans (add_le_add hOriginal hPosterior)))
  simpa only [A,G,O,P,H,Set.inter_def,Set.mem_ofPred_eq,and_assoc,add_assoc] using hh

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
