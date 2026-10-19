-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientGridMeasurable

/-! Transfer of the pointwise Brownian short-cell estimate to the posterior
joint law. The source tensor regularity event is kept explicit. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalDynamics SphericalMarkedWindows ConditionedEntrance.PhysicalHitting
open SphericalRotationCovariance SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

/-- Two applications of Fubini transfer a genuine fiber bound to a product
probability law. This is used with original Gaussian coefficients, uniform
sphere start, and Wiener noise. -/
theorem triple_prod_real_le_of_good_fibers
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {E : Set (X×(Y×Z))} (hE : MeasurableSet E)
    {G : Set X} (hG : MeasurableSet G)
    {P : Set Y} (hP : ∀ᵐ y ∂μY,y∈P)
    {c : ℝ} (hc : 0≤c)
    (hfiber : ∀ x∈G, ∀ y∈P, μZ.real {z | (x,(y,z))∈E}≤c) :
    (μX.prod (μY.prod μZ)).real {q | q.1∈G ∧ q∈E}≤c := by
  let A : Set (X×(Y×Z)) := {q | q.1∈G ∧ q∈E}
  have hA : MeasurableSet A := (hG.preimage measurable_fst).inter hE
  have hsectionY (x : X) (hx : x∈G) :
      (μY.prod μZ) {q | (x,q)∈E}≤ENNReal.ofReal c := by
    have hEx : MeasurableSet {q : Y×Z | (x,q)∈E} :=
      hE.preimage (measurable_const.prodMk measurable_id)
    rw [Measure.prod_apply hEx]
    calc
      _≤∫⁻ _y,ENNReal.ofReal c ∂μY := by
        apply lintegral_mono_ae
        filter_upwards [hP] with y hy
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
        simpa only [Set.preimage, Set.mem_ofPred_eq,
          ENNReal.toReal_ofReal hc, Measure.real] using hfiber x hx y hy
      _=ENNReal.ofReal c := by simp
  have hsectionX (x : X) :
      (μY.prod μZ) {q | (x,q)∈A}≤ENNReal.ofReal c := by
    by_cases hx : x∈G
    · have he : {q | (x,q)∈A}={q | (x,q)∈E} := by ext q; simp [A,hx]
      rw [he]
      exact hsectionY x hx
    · have he : {q | (x,q)∈A}=∅ := by ext q; simp [A,hx]
      simp [he]
  have hmass : (μX.prod (μY.prod μZ)) A≤ENNReal.ofReal c := by
    rw [Measure.prod_apply hA]
    calc
      _≤∫⁻ _x,ENNReal.ofReal c ∂μX := lintegral_mono hsectionX
      _=ENNReal.ofReal c := by simp
  exact (ENNReal.toReal_mono (by finiteness) hmass).trans_eq
    (ENNReal.toReal_ofReal hc)

theorem gridStart_add_le_horizon_two_cells (H T : ℝ≥0) (hT : 0<T)
    (j : Fin (gridSize H T)) (v : ℝ≥0) (hv : v≤T) :
    gridStart T j.val+v≤H+2*T := by
  have hTr : (0:ℝ)<T := hT
  have hj : ((j.val:ℝ)+1)≤(gridSize H T:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  have hsize := gridSize_upper H T
  have hdiv : (j.val:ℝ)≤(H:ℝ)/(T:ℝ)+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hdiv hTr.le
  have hr : ((gridStart T j.val+v:ℝ))≤((H+2*T:ℝ≥0):ℝ) := by
    change (j.val:ℝ)*(T:ℝ)+(v:ℝ)≤(H:ℝ)+2*(T:ℝ)
    have hvr : (v:ℝ)≤(T:ℝ) := hv
    have hcut : ((H:ℝ)/(T:ℝ)+1)*(T:ℝ)=(H:ℝ)+(T:ℝ) := by
      field_simp [hTr.ne']
    rw [hcut] at hmul
    linarith
  exact NNReal.coe_le_coe.mp hr

theorem mixedPosterior_score_grid_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ)
    (S H T : ℝ≥0) (hT : 0<T) (hS : H+2*T≤S)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1),
      ∀ j : Fin (gridSize H T), ∀ v : ℝ≥0, v≤T →
        mixedPosteriorOriginalGradientScore n μ Q u marks β S
          (gridStart T j.val+v) (z,(x,ω)) =
          gradientScore
            (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
              (unpackDisorder z)) u)
            (mixedProcess μ (unpackDisorder (mixedPosterior n μ Q u marks z))
              β x (gridStart T j.val+v) ω) := by
  filter_upwards [mixedPosteriorContinuousPath_ae_actual n μ Q u marks β S z x]
    with ω hω
  intro j v hv
  have ht : gridStart T j.val+v≤S :=
    (gridStart_add_le_horizon_two_cells H T hT j v hv).trans hS
  unfold mixedPosteriorOriginalGradientScore
  rw [clippedGradientScore_of_le _ _ _ ht]
  exact congrArg (gradientScore
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder z)) u)) (hω ⟨_,⟨zero_le,ht⟩⟩)

theorem mixedPosterior_badGrid_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ)
    (S H T : ℝ≥0) (hT : 0<T) (hS : H+2*T≤S)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1))
    (δ : ℝ) :
    {ω | (z,(x,ω))∈badGrid
      (mixedPosteriorOriginalGradientScore n μ Q u marks β S) H T δ} =ᵐ[VectorBrownian.law (n+1)]
    badGrid (fun t ω=>gradientScore
      (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder z)) u)
      (mixedProcess μ (unpackDisorder (mixedPosterior n μ Q u marks z)) β x t ω))
      H T δ := by
  filter_upwards [mixedPosterior_score_grid_ae_actual n μ Q u marks β S H T hT hS z x]
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

theorem mixedPosterior_regular_badGrid_brownian_bound
    (n : ℕ) (μ : FiniteMixture) (hnp : μ.minDegree<μ.maxDegree)
    (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e k : ℝ)
    (z : EuclideanDisorder (n+1) μ.maxDegree)
    (hz : unpackDisorder z∈regularDisorder)
    (β : ℝ) (hβ : 0≤β) (x : Vector (n+1)) (hx : OnSphere x)
    {α : ℝ} (hα : 0<α)
    (S H T : ℝ≥0) (hT : 0<T) (hS : H+2*T≤S)
    (hshort : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ)≤
      α/(2*centerConstant μ Q)) :
    (VectorBrownian.law (n+1)).real
      {ω | (z,(x,ω))∈badGrid
        (mixedPosteriorOriginalGradientScore n μ Q u
          (scorePairEquiv (e,k)) β S) H T (α/2)} ≤
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*(α/(2*centerConstant μ Q))^2/
          (16*(T:ℝ))) := by
  rw [measureReal_congr
    (mixedPosterior_badGrid_ae_actual n μ Q u (scorePairEquiv (e,k))
      β S H T hT hS z x (α/2))]
  exact actual_mixedPosterior_gradient_shortCells n μ hnp Q hQ hQ1 u hu
    e k z hz hβ x hx hα H T hT hshort

/-- The Brownian short-cell error is integrated under the actual original
Gaussian tensor, independent uniform spherical start, and Wiener law. The
original regularity event is explicit; its exceptional probability is handled
separately by the source tensor concentration theorem. -/
theorem mixedPosterior_regular_badGrid_joint_bound
    (n : ℕ) (μ : FiniteMixture) (hnp : μ.minDegree<μ.maxDegree)
    (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e k : ℝ)
    (β : ℝ) (hβ : 0≤β)
    {α : ℝ} (hα : 0<α)
    (S H T : ℝ≥0) (hT : 0<T) (hS : H+2*T≤S)
    (hshort : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ)≤
      α/(2*centerConstant μ Q)) :
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1∈regularDisorder ∧
        q∈badGrid
          (mixedPosteriorOriginalGradientScore n μ Q u (scorePairEquiv (e,k)) β S)
          H T (α/2)} ≤
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*(α/(2*centerConstant μ Q))^2/
          (16*(T:ℝ))) := by
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree) :=
    {z | unpackDisorder z∈regularDisorder}
  have hG : MeasurableSet G :=
    (regularDisorder_measurable _ _).preimage (by unfold unpackDisorder; fun_prop)
  have hP : ∀ᵐ x ∂sphereLaw (n+1), x∈{x : Vector (n+1) | OnSphere x} := by
    filter_upwards [sphereLaw_support (N:=n+1) (by omega)] with x hx
    exact (onSphere_iff_norm_sq x).mpr hx
  have hE := mixedPosterior_badGrid_measurable n μ Q u
    (scorePairEquiv (e,k)) β S H T (α/2)
  change ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
    ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).real _ ≤ _
  exact triple_prod_real_le_of_good_fibers
    (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
    (sphereLaw (n+1)) (VectorBrownian.law (n+1)) hE hG hP
    (by positivity)
    (fun z hz x hx =>
      mixedPosterior_regular_badGrid_brownian_bound n μ hnp Q hQ hQ1
        u hu e k z hz β hβ x hx hα S H T hT hS hshort)

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
