-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientIndependence

/-! True full posterior trajectory independence from the original center
tangent gradient, including genuine independent uniform start and Wiener noise. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalRotationCovariance
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem product_noise_rearrange {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    (μ : Measure A) (ν : Measure B) (τ : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure τ] :
    ((μ.prod ν).prod τ).map (fun q : (A×B)×Z=>((q.1.1,q.2),q.1.2))=(μ.prod τ).prod ν := by
  apply Measure.ext_prod₃_iff'.mpr
  intro s t u hs ht hu
  rw [Measure.map_apply (by fun_prop) ((hs.prod ht).prod hu)]
  have he : (fun q : (A×B)×Z=>((q.1.1,q.2),q.1.2)) ⁻¹' ((s×ˢt)×ˢu)=(s×ˢu)×ˢt := by
    ext q
    simp only [mem_preimage,mem_prod]
    tauto
  rw [he,Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,Measure.prod_prod]
  ring

theorem independent_pair_extend_noise {Ω A B Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    (μ : Measure Ω) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω→A) (g : Ω→B) (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    IndepFun (fun q : Ω×Z=>(f q.1,q.2)) (fun q : Ω×Z=>g q.1) (μ.prod ν) := by
  have hJoint : (μ.prod ν).map (fun q : Ω×Z=>((f q.1,g q.1),q.2))=
      (μ.map (fun ω=>(f ω,g ω))).prod ν := by
    change (μ.prod ν).map (Prod.map (fun ω=>(f ω,g ω)) id)=_
    simpa only [Prod.map,id_eq,Measure.map_id] using
      (Measure.map_prod_map μ ν (hf.prodMk hg) measurable_id).symm
  have hF : (μ.prod ν).map (fun q : Ω×Z=>(f q.1,q.2))=(μ.map f).prod ν := by
    change (μ.prod ν).map (Prod.map f id)=_
    simpa only [Prod.map,id_eq,Measure.map_id] using
      (Measure.map_prod_map μ ν hf measurable_id).symm
  have hG : (μ.prod ν).map (fun q : Ω×Z=>g q.1)=μ.map g := by
    rw [← Function.comp_def,← Measure.map_map hg measurable_fst,Measure.map_fst_prod,
      measure_univ,one_smul]
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
  have he : (fun q : Ω×Z=>((f q.1,q.2),g q.1))=
      (fun q : (A×B)×Z=>((q.1.1,q.2),q.1.2)) ∘ (fun q : Ω×Z=>((f q.1,g q.1),q.2)) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),hJoint,
    hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    product_noise_rearrange,hF,hG]

def posteriorTrajectoryLaw (n : ℕ) (μ : FiniteMixture) :
    Measure (EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))) :=
  (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
    ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))

instance posteriorTrajectoryLaw_probability (n : ℕ) (μ : FiniteMixture) :
    IsProbabilityMeasure (posteriorTrajectoryLaw n μ) := by
  unfold posteriorTrajectoryLaw
  infer_instance

def mixedPosteriorContinuousPath (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))) :
    ContinuousPath (n+1) T :=
  SphericalRotationCovariance.jointContinuousPath μ β T
    ((unpackDisorder (mixedPosterior n μ Q u marks q.1),q.2.1),q.2.2)

def valuePosteriorContinuousPath (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (T : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))) :
    ContinuousPath (n+1) T :=
  SphericalRotationCovariance.jointContinuousPath μ β T
    ((unpackDisorder (valuePosterior n μ Q u mark q.1),q.2.1),q.2.2)

theorem mixedPosteriorContinuousPath_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0) :
    Measurable (mixedPosteriorContinuousPath n μ Q u marks β T) := by
  have hp : Measurable (mixedPosterior n μ Q u marks) :=
    ((mixedPosterior_continuous n μ Q).comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)).measurable
  unfold mixedPosteriorContinuousPath
  exact (SphericalRotationCovariance.jointContinuousPath_measurable μ β T).comp
    (((((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp).comp measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem valuePosteriorContinuousPath_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (mark : ℝ) (β : ℝ) (T : ℝ≥0) :
    Measurable (valuePosteriorContinuousPath n μ Q u mark β T) := by
  have hp : Measurable (valuePosterior n μ Q u mark) :=
    ((valuePosterior_continuous n μ Q).comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)).measurable
  unfold valuePosteriorContinuousPath
  exact (SphericalRotationCovariance.jointContinuousPath_measurable μ β T).comp
    (((((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp).comp measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem mixedPosteriorContinuousPath_ae_actual (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : PathTime T,
      mixedPosteriorContinuousPath n μ Q u marks β T (z,(x,ω)) t=
        SphericalDynamics.mixedProcess μ (unpackDisorder (mixedPosterior n μ Q u marks z)) β x t.1 ω := by
  unfold mixedPosteriorContinuousPath
  exact jointContinuousPath_ae_actual μ β T (unpackDisorder (mixedPosterior n μ Q u marks z),x)

theorem valuePosteriorContinuousPath_ae_actual (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (mark : ℝ) (β : ℝ) (T : ℝ≥0)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : PathTime T,
      valuePosteriorContinuousPath n μ Q u mark β T (z,(x,ω)) t=
        SphericalDynamics.mixedProcess μ (unpackDisorder (valuePosterior n μ Q u mark z)) β x t.1 ω := by
  unfold valuePosteriorContinuousPath
  exact jointContinuousPath_ae_actual μ β T (unpackDisorder (valuePosterior n μ Q u mark z),x)

theorem mixedPosteriorContinuousPath_independent_original_gradient (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0) :
    IndepFun (mixedPosteriorContinuousPath n μ Q u marks β T)
      (fun q : EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))=>
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
      (posteriorTrajectoryLaw n μ) := by
  have hp : Measurable (mixedPosterior n μ Q u marks) := by
    exact ((mixedPosterior_continuous n μ Q).comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)).measurable
  have hG : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) := by
    have he : (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u)=
        surfaceGamma (centerCoefficients (mixtureCoefficients μ) Q) u := by
      funext g
      simp only [surfaceGamma,ContinuousLinearMap.comp_apply,IntrinsicGradientRegression.ambientGradientCLM_apply]
      rfl
    rw [he]
    exact (surfaceGamma _ u).continuous.measurable
  have hI := independent_pair_extend_noise (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
    ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1))) _ _ hp hG
    (mixedPosterior_independent_original_gradient n μ hQ u hu marks)
  have hObs : Measurable (fun z : EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))=>
      SphericalRotationCovariance.jointContinuousPath μ β T ((unpackDisorder z.1,z.2.1),z.2.2)) :=
    (SphericalRotationCovariance.jointContinuousPath_measurable μ β T).comp
      ((((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  unfold mixedPosteriorContinuousPath posteriorTrajectoryLaw
  simpa only [Function.comp_def,id_eq] using hI.comp hObs measurable_id

theorem valuePosteriorContinuousPath_independent_original_gradient (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (mark : ℝ) (β : ℝ) (T : ℝ≥0) :
    IndepFun (valuePosteriorContinuousPath n μ Q u mark β T)
      (fun q : EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))=>
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
      (posteriorTrajectoryLaw n μ) := by
  have hp : Measurable (valuePosterior n μ Q u mark) := by
    exact ((valuePosterior_continuous n μ Q).comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)).measurable
  have hG : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) := by
    have he : (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u)=
        surfaceGamma (centerCoefficients (mixtureCoefficients μ) Q) u := by
      funext g
      simp only [surfaceGamma,ContinuousLinearMap.comp_apply,IntrinsicGradientRegression.ambientGradientCLM_apply]
      rfl
    rw [he]
    exact (surfaceGamma _ u).continuous.measurable
  have hI := independent_pair_extend_noise (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
    ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1))) _ _ hp hG
    (valuePosterior_independent_original_gradient n μ hQ u hu mark)
  have hObs : Measurable (fun z : EuclideanDisorder (n+1) μ.maxDegree×(Vector (n+1)×VectorBrownian.Space (n+1))=>
      SphericalRotationCovariance.jointContinuousPath μ β T ((unpackDisorder z.1,z.2.1),z.2.2)) :=
    (SphericalRotationCovariance.jointContinuousPath_measurable μ β T).comp
      ((((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  unfold valuePosteriorContinuousPath posteriorTrajectoryLaw
  simpa only [Function.comp_def,id_eq] using hI.comp hObs measurable_id

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
