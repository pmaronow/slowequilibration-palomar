module

public import SphericalAging.ActualSphereSemigroup
public import SphericalAging.SharpRadialMoment
public import SphericalAging.SphereCanonicalGenerator

public section

/-! Genuine coordinate Dynkin identities obtained from the actual physical
strong SDE and the zero expectation of its constructed full-filtration Itô
integral. No generator, Markov or PDE identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCoordinateDynkin
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open AnnealedSDECore SharpRadialMoment
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The expected actual coordinate is its expected initial state plus the
integral of its expected actual drift. -/
theorem coordinate_expectation_eq (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (t : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X t) (hmZ : MemLp Z0 2 P)
    (i : Fin N)
    (hHa : StronglyAdapted F (fun s ω => b ω i (X s ω)))
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => b ω i (X s ω)))
    (K : ℝ≥0) (hbound : ∀ᵐ ω ∂P,∀ s,‖b ω i (X s ω)‖ ≤ K) :
    (∫ ω,X t ω i ∂P) = (∫ ω,Z0 ω i ∂P)+
      ∫ s in (0 : ℝ)..(t : ℝ),∫ ω,b ω i (X s.toNNReal ω) ∂P := by
  obtain ⟨A,U,hA,hU,hEq⟩ := hX.2.2.2
  have h0i := (RandomInitialSDE.coordinateInitial_memLp Z0 hX.1 hmZ i).integrable (by norm_num)
  have hAi := (driftVersion_memLp (A i) t t).integrable (by norm_num)
  have hUi := (Lp.memLp (VectorIto.vectorProcessLp D (U i) t)).integrable (by norm_num)
  have heq : (fun ω => X t ω i) =ᵐ[P] (fun ω => Z0 ω i+driftVersion (A i) t t ω+
      (VectorIto.vectorProcessLp D (U i) t : Ω → ℝ) ω) := by
    filter_upwards [hEq t le_rfl i,driftVersion_eq_actual (A i)
      (fun s ω => b ω i (X s ω)) t (hA i)] with ω he hd
    rw [hd t le_rfl]
    exact he
  have he : (∫ ω,X t ω i ∂P) = (∫ ω,Z0 ω i ∂P)+∫ ω,driftVersion (A i) t t ω ∂P := by
    rw [integral_congr_ae heq]
    have h1 := integral_add (h0i.add hAi) hUi
    have h2 := integral_add h0i hAi
    simp only [Pi.add_apply] at h1 h2
    rw [h1,h2,vectorProcessLp_expectation_zero]
    simp
  rw [he,expectation_driftVersion]
  congr 1
  have hcut : cutRepresentative (A i) t =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => b ω i (X s ω)) t := by
    filter_upwards [representative_ae (A i),hA i] with q hr ha
    simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator,Set.mem_prod,Set.mem_univ,and_true,FourPapersCommon.continuousAdaptedTimeCut,hr,ha]
    split <;> rfl
  rw [integral_congr_ae hcut,integral_prod _ (timeCut_integrable _ hHa hHc K hbound t)]
  have hprim : (∫ s in Ioc (0 : ℝ≥0) t,∫ ω,b ω i (X s ω) ∂P ∂nonnegativeLebesgueMeasure) =
      ∫ s in (0 : ℝ)..(t : ℝ),∫ ω,b ω i (X s.toNNReal ω) ∂P :=
    primitive_eq_real_intervalIntegral (fun q : ℝ≥0 × Unit => ∫ ω,b ω i (X q.1 ω) ∂P) t ()
  rw [← hprim,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun s => by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) t <;>
      simp [FourPapersCommon.continuousAdaptedTimeCut,hs])

/-- Physical Hamiltonian drift is uniformly bounded along any sphere-valued
path, by the actual compact cutoff estimate. -/
theorem physical_drift_bound (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (X : ℝ≥0 → Ω → State N) (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) :
    ∃ K : ℝ≥0,∀ᵐ ω ∂P,∀ s i,‖hamiltonianDrift β J (X s ω) i‖ ≤ K := by
  obtain ⟨K,hK⟩ := cutoffCoefficient_bounded R hR (hamiltonianDrift β J)
    (contDiff_hamiltonianDrift β J).continuous
  have hKn : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨⟨K,hKn⟩,?_⟩
  filter_upwards [hXs] with ω hω
  intro s i
  have hn : ‖X s ω‖^2 = (N : ℝ) := by
    simpa only [OnSphere,real_inner_self_eq_norm_sq] using hω s
  have hnorm : ‖X s ω‖ ≤ R := by nlinarith [norm_nonneg (X s ω)]
  have hb := hK (X s ω)
  rw [cutoffCoefficient_eq R hR _ _ hnorm] at hb
  exact (PiLp.norm_apply_le _ i).trans hb

/-- Actual coordinate Dynkin equation on the sphere, for arbitrary
correlated random initial state and the genuine physical Hamiltonian SDE. -/
theorem physical_coordinate_expectation_eq (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D (fun _ i x => hamiltonianDrift β J x i)
      (fun _ i j x => noiseColumn x j i) Z0 X T) (hmZ : MemLp Z0 2 P)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (t : ℝ≥0) (i : Fin N) :
    (∫ ω,X t ω i ∂P) = (∫ ω,Z0 ω i ∂P)+
      ∫ s in (0 : ℝ)..(t : ℝ),∫ ω,hamiltonianDrift β J (X s.toNNReal ω) i ∂P := by
  obtain ⟨K,hK⟩ := physical_drift_bound β J R hR hNR X hXs
  have hc : Continuous (fun x : State N => hamiltonianDrift β J x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp
      (contDiff_hamiltonianDrift β J).continuous
  apply coordinate_expectation_eq D t (hX t) hmZ i
    (fun s => hc.comp_stronglyMeasurable ((hX 0).2.1 s))
    (((hX 0).2.2.1).mono (fun ω hω => hc.comp hω)) K
  exact hK.mono (fun ω hω s => hω s i)

/-- Positive-time differentiation of the genuine physical expected
coordinate, with the expected actual drift as derivative. -/
theorem physical_coordinate_hasDerivAt (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D (fun _ i x => hamiltonianDrift β J x i)
      (fun _ i j x => noiseColumn x j i) Z0 X T) (hmZ : MemLp Z0 2 P)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (t : ℝ) (ht : 0 < t) (i : Fin N) :
    HasDerivAt (fun s : ℝ => ∫ ω,X s.toNNReal ω i ∂P)
      (∫ ω,hamiltonianDrift β J (X t.toNNReal ω) i ∂P) t := by
  obtain ⟨K,hK⟩ := physical_drift_bound β J R hR hNR X hXs
  have hc : Continuous (fun x : State N => hamiltonianDrift β J x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp
      (contDiff_hamiltonianDrift β J).continuous
  have hmean : Continuous (fun s : ℝ => ∫ ω,hamiltonianDrift β J (X s.toNNReal ω) i ∂P) :=
    (firstMoment_continuous (P := P) (fun s ω => hamiltonianDrift β J (X s ω) i)
      (fun s => hc.comp_stronglyMeasurable ((hX 0).2.1 s))
      (((hX 0).2.2.1).mono (fun ω hω => hc.comp hω)) K
      (hK.mono (fun ω hω s => hω s i))).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) t) (hmean.stronglyMeasurableAtFilter volume (𝓝 t))
    hmean.continuousAt).const_add (∫ ω,Z0 ω i ∂P)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [physical_coordinate_expectation_eq D β J R hR hNR hX hmZ hXs s.toNNReal i,
    Real.coe_toNNReal _ hs.le]

/-- The actual coefficient generator on a linear coordinate is exactly
the corresponding Hamiltonian drift coordinate. -/
theorem coefficientGenerator_coordinate (β : ℝ) (J : FiniteModel.Disorder N p)
    (i : Fin N) (x : State N) :
    SphereGenerator.coefficientGenerator β J (fun y : State N => y i) x =
      hamiltonianDrift β J x i := by
  let c : State N →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i
  have h1 : fderiv ℝ (fun y : State N => y i) = fun _ => c := by
    funext y
    exact c.fderiv
  unfold SphereGenerator.coefficientGenerator
  rw [h1]
  have h2 : fderiv ℝ (fun _ : State N => c) x = 0 := by
    exact fderiv_const_apply c
  rw [h2]
  simp [c]

/-- The genuine expectation derivative is the expectation of the actual
Itô coefficient generator, for each coordinate observable. -/
theorem physical_coordinate_generator_hasDerivAt (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D (fun _ i x => hamiltonianDrift β J x i)
      (fun _ i j x => noiseColumn x j i) Z0 X T) (hmZ : MemLp Z0 2 P)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (t : ℝ) (ht : 0 < t) (i : Fin N) :
    HasDerivAt (fun s : ℝ => ∫ ω,X s.toNNReal ω i ∂P)
      (∫ ω,SphereGenerator.coefficientGenerator β J (fun y : State N => y i)
        (X t.toNNReal ω) ∂P) t := by
  simpa only [coefficientGenerator_coordinate] using
    physical_coordinate_hasDerivAt D β J R hR hNR hX hmZ hXs t ht i

/-- Genuine generator evolution for the actual transition expectation of
a coordinate observable. The transition is built from the global SDE. -/
theorem transition_coordinate_generator_hasDerivAt (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    (t : ℝ) (ht : 0 < t) (i : Fin N) :
    HasDerivAt (fun s : ℝ => ActualSphereTransition.transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal
        (fun y : State N => y i) x)
      (ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J t.toNNReal
          (SphereGenerator.coefficientGenerator β J (fun y : State N => y i)) x) t := by
  exact physical_coordinate_generator_hasDerivAt
    (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR hNR
    (fun T => ActualSphereMarkovRestart.jointProcess_physical hN (VectorBrownian.driver N)
      β R hR hNR J x hx T) (memLp_const x)
    (ActualSphereTransition.jointProcess_onSphere hN (VectorBrownian.driver N)
      β R hR hNR J x hx) t ht i

/-- The canonical rotation generator has the genuine physical drift as
its value on every coordinate observable on the sphere. -/
theorem canonicalGenerator_coordinate (hN : 0 < N) (β : ℝ)
    (J : FiniteModel.Disorder N p) (i : Fin N) (x : State N) (hx : OnSphere x) :
    SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
      (fun ij : Fin N × Fin N => SphereRotationGeometry.coordinateRotation ij.1 ij.2)
        (fun y : State N => y i) x = hamiltonianDrift β J x i := by
  rw [SphereCanonicalGenerator.canonical_rotationGenerator_eq_coefficientGenerator hN β J
    (show ContDiff ℝ 2 (fun y : State N => y i) from
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff) x hx]
  exact coefficientGenerator_coordinate β J i x

/-- The canonical rotation generator occurs in the positive-time evolution
of the actual coordinate transition expectation. -/
theorem transition_coordinate_canonicalGenerator_hasDerivAt (hN : 0 < N)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    (t : ℝ) (ht : 0 < t) (i : Fin N) :
    HasDerivAt (fun s : ℝ => ActualSphereTransition.transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal
        (fun y : State N => y i) x)
      (ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J t.toNNReal
          (SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
            (fun ij : Fin N × Fin N => SphereRotationGeometry.coordinateRotation ij.1 ij.2)
              (fun y : State N => y i)) x) t := by
  have hd := transition_coordinate_generator_hasDerivAt (Nat.ne_of_gt hN)
    β R hR hNR J x hx t ht i
  have he : ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t.toNNReal (SphereGenerator.coefficientGenerator β J (fun y : State N => y i)) x =
    ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t.toNNReal
        (SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
          (fun ij : Fin N × Fin N => SphereRotationGeometry.coordinateRotation ij.1 ij.2)
            (fun y : State N => y i)) x := by
    apply integral_congr_ae
    filter_upwards [ActualSphereTransition.jointProcess_onSphere (Nat.ne_of_gt hN)
      (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
    rw [coefficientGenerator_coordinate,canonicalGenerator_coordinate hN β J i _ (hω t.toNNReal)]
  rw [he] at hd
  exact hd

end SphericalAging.ActualCoordinateDynkin
