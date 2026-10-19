module

public import SphericalAging.ActualSphereTransition
public import SphericalAging.BrownianFutureFiltered
public import SphericalAging.FilteredRandomSDEPullback
public import SphericalAging.RandomSDEConversions
public import SphericalAging.AnnealedPhysicalUniqueness
public import SphericalAging.ShiftedRandomSDE

public section

/-! The actual physical future is the jointly measurable fixed-disorder
flow evaluated at the observed waiting state and actual future Wiener
path. The product law, full filtered Itô pullback, and physical pathwise
uniqueness are proved; no Markov restart identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereMarkovRestart
open HardSphereDynamics ActualSphereTransition HamiltonianPicardDependence
open GlobalHamiltonianParameter RandomSDEConversions AnnealedSDECore
open BrownianFuturePath BrownianFutureFiltered FilteredRandomSDEPullback
set_option maxHeartbeats 2400000
variable {N p : ℕ}

/-- The measurable joint family remains the actual physical strong solution. -/
theorem jointProcess_physical {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hN : N ≠ 0) (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    IsRandomStrongSolutionOn (NullAugmentation.driver D₀)
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i)
      (fun _ => x) (jointProcess (NullAugmentation.driver D₀) β R hR (J,x)) T := by
  let D := NullAugmentation.driver D₀
  let X := HamiltonianJointProcess.globalProcess D β R hR (J,x)
  let Y := jointProcess D β R hR (J,x)
  have hsphere := globalProcess_onSphere hN D₀ β R hR hNR J x hx
  have hbound : ∀ᵐ ω ∂P,∀ t,‖X t ω‖ ≤ R := by
    filter_upwards [hsphere] with ω hω
    intro t
    have hsq := (onSphere_iff_norm_sq _).mp (hω t)
    nlinarith [norm_nonneg (X t ω),R.coe_nonneg]
  have hcut := GlobalSDE.process_strongSolution D
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (noise_family_lipschitz N R hR) x T
  have hphysical : LocalSDE.IsLocalStrongSolutionOn
      (fun i z => hamiltonianDrift β J z i) (fun i j z => noiseColumn z j i)
      CutoffSphere.physical_noise_continuous D x X T :=
    CutoffSphere.coefficient_congr_onPath CutoffSphere.physical_noise_continuous hcut
    (fun i => hbound.mono (fun ω h t _ => (CutoffSDE.cutoffDrift_eq β J R hR _ (h t) i).symm))
    (fun i j => hbound.mono (fun ω h t _ => (CutoffSDE.cutoffNoise_eq N R hR _ (h t) i j).symm))
  have hYa : StronglyAdapted (NullAugmentation.augment F P) Y := by
    intro t
    exact (jointProcess_adapted D β R hR t).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hYc : ∀ᵐ ω ∂P,Continuous (fun t => Y t ω) :=
    ((HamiltonianJointProcess.exists_joint_adapted_global_process D β R hR).choose_spec.2.2 (J,x)).mono
      (fun _ h => h.2)
  have hsol := AllPathSDE.IsLocalStrongSolutionOn.path_congr hphysical hYa hYc
    (jointProcess_ae D β R hR (J,x))
  exact localStrongSolution_to_random
    (fun i => (CutoffSDE.coordinate_lipschitz i).continuous.comp (contDiff_hamiltonianDrift β J).continuous) hsol

/-- On a product initial/disorder law, the actual constructed process and
joint family have the same terminal value. -/
theorem annealedGlobal_eq_joint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {ρ : Measure (AnnealedCutoffProcess.Parameter N p)} [IsProbabilityMeasure ρ]
    (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : AnnealedCutoffProcess.Parameter N p => q.1) 2 ρ) (t : ℝ≥0) :
    (fun ω => AnnealedGlobalSDE.globalProcess D β R hR hJ t ω) =ᵐ[ρ.prod P]
      (fun ω => jointProcess D β R hR ω.1 t ω.2) := by
  have hm1 := (AnnealedGlobalSDE.globalProcess_stronglyAdapted D β R hR hJ t).mono
    ((IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p) F).le t)
  have hm2 : StronglyMeasurable (fun ω : AnnealedCutoffProcess.Parameter N p × Ω =>
      jointProcess D β R hR ω.1 t ω.2) :=
    (jointProcess_measurable D β R hR).comp_measurable
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae (hm1.measurableSet_eq_fun hm2)).mpr
  filter_upwards [AnnealedCutoffProcess.process_slice_global D β R hR hJ
    (GlobalSDE.integerHorizon (Nat.ceil t))] with q hq
  filter_upwards [hq,jointProcess_ae D β R hR q] with ω hq hj
  exact (hq t (GlobalSDE.le_integerHorizon_ceil t)).trans (hj t).symm

/-- True random waiting-state evaluation of the actual future path. -/
theorem actual_future_eq_joint (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (X : ℝ≥0 → VectorBrownian.Space N → State N)
    {Z0 : VectorBrownian.Space N → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i)
      Z0 X T)
    (hXs : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) (s t : ℝ≥0) :
    (fun ω => X (s+t) ω) =ᵐ[VectorBrownian.law N]
      (fun ω => jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
        (J,X s ω) t (future s ω)) := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let Z : VectorBrownian.Space N → AnnealedCutoffProcess.Parameter N p := fun ω => (J,X s ω)
  have hZa : Measurable[F s] Z := measurable_const.prodMk (((hX 0).2.1 s).measurable)
  have hZm : Measurable Z := hZa.mono (F.le s) le_rfl
  let ρ := P.map Z
  have hρ : IsProbabilityMeasure ρ :=
    (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  letI := hρ
  have hdisorder : ∀ᵐ q ∂ρ,q.1=J := by
    apply (ae_map_iff hZm.aemeasurable (measurable_fst (MeasurableSet.singleton J))).mpr
    exact .of_forall (fun _ => rfl)
  have hJ : MemLp (fun q : AnnealedCutoffProcess.Parameter N p => q.1) 2 ρ :=
    MemLp.of_bound measurable_fst.aestronglyMeasurable ‖J‖
      (hdisorder.mono (fun q h => by rw [h]))
  have hinitial : ∀ᵐ q ∂ρ,OnSphere q.2 := by
    apply (ae_map_iff hZm.aemeasurable ?_).mpr
    · exact hXs.mono (fun _ h => h s)
    · simpa only [OnSphere,real_inner_self_eq_norm_sq,Pi.pow_apply] using
        (isClosed_eq (continuous_snd.norm.pow 2) (continuous_const (y := (N : ℝ)))).measurableSet
  let E := IndependentBackgroundDriver.driver (ρ := ρ) D
  let Y := AnnealedGlobalSDE.globalProcess D β R hR hJ
  have hY := AnnealedGlobalSDE.globalProcess_physical hN (VectorBrownian.driver N)
    β R hR hNR hJ hinitial
  let φ : VectorBrownian.Space N → AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N :=
    fun ω => (Z ω,future s ω)
  have hφ : MeasurePreserving φ P (ρ.prod P) := waiting_future_measurePreserving s Z hZa
  have hφF : ∀ u,@Measurable (VectorBrownian.Space N)
      (AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N)
      (ShiftedBrownian.filtration F s u)
      (IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p) F u) φ :=
    waiting_future_filtered s Z hZa
  have hB : ∀ i u,(ShiftedBrownian.driver D s).coordinate i u =ᵐ[P]
      (fun ω => E.coordinate i u (φ ω)) := fun _ _ => .of_forall (fun _ => rfl)
  have hYpull : ∀ T,IsRandomStrongSolutionOn (ShiftedBrownian.driver D s)
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i)
      (X s) (fun u ω => Y u (φ ω)) T := by
    intro T
    exact randomStrongSolution_pullback hφ hφF E (ShiftedBrownian.driver D s) hB
      _ _ _ _ T (hY.1 T)
  have hYps : ∀ᵐ ω ∂P,∀ u,OnSphere (Y u (φ ω)) := hφ.quasiMeasurePreserving.ae hY.2
  have hXfuture : ∀ T,IsRandomStrongSolutionOn (ShiftedBrownian.driver D s)
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i)
      (X s) (ShiftedSDE.stateShift X s) T := by
    intro T
    exact ShiftedRandomSDE.randomStrongSolution_timeShift D _ _
      (fun _ i => (CutoffSDE.coordinate_lipschitz i).continuous.comp
        (contDiff_hamiltonianDrift β J).continuous) Z0 X s T (hX (s+T))
  have he := AnnealedPhysicalUniqueness.physical_global_pathwise_uniqueness
    (ShiftedBrownian.driver D s) β (fun _ => J) stronglyMeasurable_const (X s)
    (ShiftedSDE.stateShift X s) (fun u ω => Y u (φ ω)) hXfuture hYpull
    (ShiftedRandomSDE.stateShift_onSphere X hXs s) hYps
  have hj := hφ.quasiMeasurePreserving.ae (annealedGlobal_eq_joint D β R hR hJ t)
  filter_upwards [he,hj] with ω he hj
  exact (he t).trans hj

end SphericalAging.ActualSphereMarkovRestart
