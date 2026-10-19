module

public import SphericalAging.PhysicalC2Ito
public import SphericalAging.ActualCoordinateDynkin

public section

/-! Actual general C² Dynkin expectation and generator evolution for the
constructed Hamiltonian sphere SDE. Neither Markov nor PDE conclusions are
inputs to the stochastic identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualC2Dynkin
open HardSphereDynamics LocalSDE AnnealedSDECore VectorIto SharpRadialMoment
open PredictableDriftTime PhysicalC2Ito MultivariateTaylor
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma randomStrong_initial_ae (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T) : X 0=ᵐ[P] Z0 := by
  obtain ⟨A,U,hA,hU,hEq⟩ := hX.2.2.2
  have hall := ae_all_iff.mpr (fun i : Fin N => hEq 0 bot_le i)
  have hi : ∀ᵐ ω ∂P,∀ i : Fin N,(vectorProcessLp D (U i) 0 : Ω → ℝ) ω=0 :=
    ae_all_iff.mpr (fun i => by
      rw [LinearSDELocalization.vectorProcessLp_zero_time]
      exact Lp.coeFn_zero ℝ 2 P)
  filter_upwards [hall,hi] with ω hω hiω
  apply PiLp.ext
  intro i
  simpa only [NNReal.coe_zero,intervalIntegral.integral_same,add_zero,hiω i] using hω i

/-- Every continuous state observable is truly bounded along sphere paths,
by compactness of the actual physical state ball. -/
lemma sphere_observable_bound (g : State N → ℝ) (hg : Continuous g)
    (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2) (X : ℝ≥0 → Ω → State N)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) :
    ∃ K : ℝ≥0,∀ᵐ ω ∂P,∀ s,‖g (X s ω)‖≤K := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0 : State N) R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨Real.toNNReal K,?_⟩
  filter_upwards [hXs] with ω hω
  intro s
  have hn : ‖X s ω‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hω s
  have hr : ‖X s ω‖≤R := by nlinarith [norm_nonneg (X s ω)]
  exact (hK _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hr)).trans (Real.le_coe_toNNReal K)

lemma vectorIto_expectation_zero (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) : (∫ ω,(vectorIto D U : Ω → ℝ) ω ∂P)=0 := by
  unfold vectorIto
  rw [← generalExpectationMap_apply,map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [generalExpectationMap_apply]
  exact FourPapersCommon.FilteredBrownian.integral_naturalItoIntegral (D.filtered j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j) _

/-- Fubini for the actual bounded adapted continuous generator observation,
proved on the true finite physical time cut. -/
lemma expectation_time_integral (G : ℝ≥0 → Ω → ℝ) (hGa : StronglyAdapted F G)
    (hGc : ∀ᵐ ω ∂P,Continuous (fun s => G s ω)) (K : ℝ≥0)
    (hK : ∀ᵐ ω ∂P,∀ s,‖G s ω‖≤K) (T : ℝ≥0) :
    (∫ ω,(∫ s in Ioc (0 : ℝ≥0) T,G s ω ∂nonnegativeLebesgueMeasure) ∂P)=
      ∫ s in (0 : ℝ)..(T : ℝ),∫ ω,G s.toNNReal ω ∂P := by
  have hc := timeCut_integrable G hGa hGc K hK T
  have he : (fun ω => ∫ s in Ioc (0 : ℝ≥0) T,G s ω ∂nonnegativeLebesgueMeasure)=
      fun ω => ∫ s,FourPapersCommon.continuousAdaptedTimeCut G T (s,ω) ∂nonnegativeLebesgueMeasure := by
    funext ω
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> simp [Set.indicator,FourPapersCommon.continuousAdaptedTimeCut,hs])
  rw [he,← integral_prod_symm _ hc,integral_prod _ hc]
  have hp := primitive_eq_real_intervalIntegral
    (fun q : ℝ≥0 × Unit => ∫ ω,G q.1 ω ∂P) T ()
  dsimp only [primitive] at hp
  rw [← hp,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun s => by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> simp [FourPapersCommon.continuousAdaptedTimeCut,hs])

/-- Genuine Dynkin expectation for every C² state observable on the actual
Hamiltonian sphere SDE. -/
theorem physical_C2_expectation_eq (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ ω,f (X T ω) ∂P)=(∫ ω,f (Z0 ω) ∂P)+
      ∫ s in (0 : ℝ)..(T : ℝ),∫ ω,SphereGenerator.coefficientGenerator β J f (X s.toNNReal ω) ∂P := by
  obtain ⟨V,hV,he⟩ := physical_C2_ito_formula D β J T hX hXs R hR hNR hf
  let G : ℝ≥0 → Ω → ℝ := fun s ω => SphereGenerator.coefficientGenerator β J f (X s ω)
  have hGa : StronglyAdapted F G := fun s => (generator_continuous β J hf).comp_stronglyMeasurable (hX.2.1 s)
  have hGc : ∀ᵐ ω ∂P,Continuous (fun s => G s ω) := hX.2.2.1.mono
    (fun _ hc => (generator_continuous β J hf).comp hc)
  obtain ⟨Kg,hKg⟩ := sphere_observable_bound _ (generator_continuous β J hf) R hR hNR X hXs
  obtain ⟨Kf,hKf⟩ := sphere_observable_bound f hf.continuous R hR hNR X hXs
  have hf0 : Integrable (fun ω => f (X 0 ω)) P := Integrable.of_bound
    (hf.continuous.comp_aestronglyMeasurable (((hX.2.1 0).mono (F.le 0)).aestronglyMeasurable)) Kf
    (hKf.mono (fun _ h => h 0))
  have hfZ : Integrable (fun ω => f (Z0 ω)) P := hf0.congr
    ((randomStrong_initial_ae D T hX).mono (fun _ h => congrArg f h))
  have hGI : Integrable (fun ω => ∫ s in Ioc (0 : ℝ≥0) T,G s ω ∂nonnegativeLebesgueMeasure) P := by
    have hi := (timeCut_integrable G hGa hGc Kg hKg T).integral_prod_right
    convert hi using 1
    funext ω
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> simp [Set.indicator,FourPapersCommon.continuousAdaptedTimeCut,hs])
  have hnoise := integrable_finsetSum Finset.univ
    (fun i _ => (Lp.memLp (vectorIto D (V i))).integrable (by norm_num))
  rw [integral_congr_ae he]
  have hsum := integral_add (hfZ.add hGI) hnoise
  have hfirst := integral_add hfZ hGI
  simp only [Pi.add_apply,Finset.sum_apply] at hsum hfirst
  rw [hsum,hfirst,integral_finsetSum _ (fun i _ => (Lp.memLp (vectorIto D (V i))).integrable (by norm_num))]
  simp only [vectorIto_expectation_zero,Finset.sum_const_zero,add_zero]
  congr 1
  exact expectation_time_integral G hGa hGc Kg hKg T

/-- True generator evolution for every C² observable on the actual
physical sphere process, with no backward PDE assumed. -/
theorem physical_C2_hasDerivAt (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ∫ ω,f (X s.toNNReal ω) ∂P)
      (∫ ω,SphereGenerator.coefficientGenerator β J f (X t.toNNReal ω) ∂P) t := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β J hf) R hR hNR X hXs
  have hmean : Continuous (fun s : ℝ => ∫ ω,SphereGenerator.coefficientGenerator β J f (X s.toNNReal ω) ∂P) :=
    (firstMoment_continuous (P := P) (fun s ω => SphereGenerator.coefficientGenerator β J f (X s ω))
      (fun s => (generator_continuous β J hf).comp_stronglyMeasurable ((hX 0).2.1 s))
      ((hX 0).2.2.1.mono (fun _ hc => (generator_continuous β J hf).comp hc)) K hK).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) t) (hmean.stronglyMeasurableAtFilter volume (𝓝 t))
    hmean.continuousAt).const_add (∫ ω,f (Z0 ω) ∂P)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [physical_C2_expectation_eq D β J s.toNNReal (hX s.toNNReal) hXs R hR hNR hf,
    Real.coe_toNNReal _ hs.le]

/-- General C² generator evolution of the genuine fixed-disorder
transition expectation built from the constructed sphere SDE. -/
theorem transition_C2_hasDerivAt (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ActualSphereTransition.transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal f x)
      (ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J t.toNNReal (SphereGenerator.coefficientGenerator β J f) x) t := by
  exact physical_C2_hasDerivAt (NullAugmentation.driver (VectorBrownian.driver N)) β J
    (fun T => ActualSphereMarkovRestart.jointProcess_physical hN (VectorBrownian.driver N)
      β R hR hNR J x hx T)
    (ActualSphereTransition.jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx)
    R hR hNR hf t ht

/-- The same genuine evolution expressed through the manuscript's actual
canonical rotation generator, using the proved coefficient connection. -/
theorem transition_C2_canonicalGenerator_hasDerivAt (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ActualSphereTransition.transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal f x)
      (ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J t.toNNReal
          (SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
            (fun ij : Fin N × Fin N => SphereRotationGeometry.coordinateRotation ij.1 ij.2) f) x) t := by
  have hd := transition_C2_hasDerivAt hN β R hR hNR J x hx hf t ht
  convert hd using 1
  apply integral_congr_ae
  filter_upwards [ActualSphereTransition.jointProcess_onSphere hN (VectorBrownian.driver N)
    β R hR hNR J x hx] with ω hω
  exact SphereCanonicalGenerator.canonical_rotationGenerator_eq_coefficientGenerator
    (Nat.pos_of_ne_zero hN) β J hf _ (hω t.toNNReal)

end SphericalAging.ActualC2Dynkin
