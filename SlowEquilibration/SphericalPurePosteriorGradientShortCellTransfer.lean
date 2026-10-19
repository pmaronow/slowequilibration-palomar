-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPurePosteriorGradientShortCells

/-! Transfer of the proper value-posterior short-cell estimate to the
original Gaussian, spherical start, and Brownian product law. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalDynamics SphericalMarkedWindows ConditionedEntrance.PhysicalHitting
open SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem valuePosterior_score_grid_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (e β : ℝ) (S H T : ℝ≥0) (hT : 0 < T) (hS : H+2*T ≤ S)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1),
      ∀ j : Fin (gridSize H T), ∀ v : ℝ≥0, v ≤ T →
        valuePosteriorOriginalGradientScore n μ Q u e β S
          (gridStart T j.val+v) (z,(x,ω)) =
          gradientScore
            (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
              (unpackDisorder z)) u)
            (mixedProcess μ (unpackDisorder (valuePosterior n μ Q u e z))
              β x (gridStart T j.val+v) ω) := by
  filter_upwards [valuePosteriorContinuousPath_ae_actual n μ Q u e β S z x]
    with ω hω
  intro j v hv
  have ht : gridStart T j.val+v ≤ S :=
    (gridStart_add_le_horizon_two_cells H T hT j v hv).trans hS
  unfold valuePosteriorOriginalGradientScore
  rw [clippedGradientScore_of_le _ _ _ ht]
  exact congrArg (gradientScore
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder z)) u)) (hω ⟨_,⟨zero_le,ht⟩⟩)

theorem valuePosterior_badGrid_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (e β : ℝ) (S H T : ℝ≥0) (hT : 0 < T) (hS : H+2*T ≤ S)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1))
    (δ : ℝ) :
    {ω | (z,(x,ω)) ∈ badGrid
      (valuePosteriorOriginalGradientScore n μ Q u e β S) H T δ} =ᵐ[VectorBrownian.law (n+1)]
    badGrid (fun t ω => gradientScore
      (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder z)) u)
      (mixedProcess μ (unpackDisorder (valuePosterior n μ Q u e z)) β x t ω))
      H T δ := by
  filter_upwards [valuePosterior_score_grid_ae_actual n μ Q u e β S H T hT hS z x]
    with ω hω
  simp only [badGrid,mem_ofPred_eq]
  apply propext
  constructor
  · rintro ⟨j,v,hv,hbad⟩
    refine ⟨j,v,hv,?_⟩
    have he1 := hω j v hv
    have he0 := hω j 0 (zero_le : (0 : ℝ≥0) ≤ T)
    simp only [add_zero] at he0
    rw [he1,he0] at hbad
    exact hbad
  · rintro ⟨j,v,hv,hbad⟩
    refine ⟨j,v,hv,?_⟩
    have he1 := hω j v hv
    have he0 := hω j 0 (zero_le : (0 : ℝ≥0) ≤ T)
    simp only [add_zero] at he0
    rw [he1,he0]
    exact hbad

theorem valuePosterior_regular_badGrid_brownian_bound
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e : ℝ)
    (z : EuclideanDisorder (n+1) μ.maxDegree)
    (hz : unpackDisorder z ∈ regularDisorder) (K : ℝ) (hK : 0 ≤ K)
    (hpost : unpackDisorder (valuePosterior n μ Q u e z) ∈
      sourcePosteriorOrderedRegularity K)
    (β : ℝ) (hβ : 0 ≤ β) (x : Vector (n+1)) (hx : OnSphere x)
    {α : ℝ} (hα : 0 < α)
    (S H T : ℝ≥0) (hT : 0 < T) (hS : H+2*T ≤ S)
    (hshort : 4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
      α/(2*centerConstant μ Q)) :
    (VectorBrownian.law (n+1)).real
      {ω | (z,(x,ω)) ∈ badGrid
        (valuePosteriorOriginalGradientScore n μ Q u e β S) H T (α/2)} ≤
      (gridSize H T:ℝ)*2*Real.exp (-((n+1:ℕ):ℝ)*
        (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) := by
  rw [measureReal_congr
    (valuePosterior_badGrid_ae_actual n μ Q u e β S H T hT hS z x (α/2))]
  exact actual_valuePosterior_gradient_shortCells n μ Q u hu e z hz K hK hpost
    hβ x hx hα H T hT hshort

theorem valuePosterior_regular_badGrid_joint_bound
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e : ℝ)
    (K : ℝ) (hK : 0 ≤ K) (β : ℝ) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α)
    (S H T : ℝ≥0) (hT : 0 < T) (hS : H+2*T ≤ S)
    (hshort : 4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
      α/(2*centerConstant μ Q)) :
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1 ∈ regularDisorder ∧
        unpackDisorder (valuePosterior n μ Q u e q.1) ∈ sourcePosteriorOrderedRegularity K ∧
        q ∈ badGrid (valuePosteriorOriginalGradientScore n μ Q u e β S)
          H T (α/2)} ≤
      (gridSize H T:ℝ)*2*Real.exp (-((n+1:ℕ):ℝ)*
        (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) := by
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree) :=
    {z | unpackDisorder z ∈ regularDisorder ∧
      unpackDisorder (valuePosterior n μ Q u e z) ∈ sourcePosteriorOrderedRegularity K}
  have hUnpack : Measurable (unpackDisorder (N := n+1) (P := μ.maxDegree)) := by
    unfold unpackDisorder
    fun_prop
  have hp : Measurable (valuePosterior n μ Q u e) := by
    exact ((valuePosterior_continuous n μ Q).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)).measurable
  have hG : MeasurableSet G :=
    ((regularDisorder_measurable _ _).preimage hUnpack).inter
      ((sourcePosteriorOrderedRegularity_measurable (n+1) μ.maxDegree K).preimage
        (hUnpack.comp hp))
  have hP : ∀ᵐ x ∂sphereLaw (n+1), x ∈ {x : Vector (n+1) | OnSphere x} := by
    filter_upwards [sphereLaw_support (N:=n+1) (by omega)] with x hx
    exact (onSphere_iff_norm_sq x).mpr hx
  have hE := valuePosterior_badGrid_measurable n μ Q u e β S H T (α/2)
  change ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
    ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).real _ ≤ _
  have hbound := triple_prod_real_le_of_good_fibers
    (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
    (sphereLaw (n+1)) (VectorBrownian.law (n+1)) hE hG hP
    (by positivity)
    (fun z hz x hx =>
      valuePosterior_regular_badGrid_brownian_bound n μ Q u hu e z
        hz.1 K hK hz.2 β hβ x hx hα S H T hT hS hshort)
  simpa only [G,Set.mem_ofPred_eq,and_assoc] using hbound

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
