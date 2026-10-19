module

public import SphericalAging.AnnealedCutoffProcess

public section

/-! Identification of the actual enlarged-filtration coefficient classes
with evaluation of the random-disorder Hamiltonian coefficients on the
constructed annealed paths. These are proved product almost-everywhere
identities, rather than a presumed stochastic-Fubini SDE premise.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedCutoffCoefficients
open HardSphereDynamics LocalSDE PredictableDriftTime PredictableItoTime
open IndependentBackgroundDriver HamiltonianCoefficientDependence HamiltonianFamilyIntegrability
open HamiltonianPicardDependence GlobalHamiltonianParameter AnnealedCutoffProcess
set_option maxHeartbeats 300000
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
variable {ρ : Measure (Parameter N p)} [IsProbabilityMeasure ρ]

/-- Product equality follows from genuine AE sections for AE measurable
functions as well as for everywhere measurable representatives. -/
lemma ae_eq_of_ae_sections {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] {f g : A × B → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : AEStronglyMeasurable g (μ.prod ν))
    (he : ∀ᵐ a ∂μ, (fun b => f (a,b)) =ᵐ[ν] (fun b => g (a,b))) : f =ᵐ[μ.prod ν] g := by
  have he' : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae (hf.stronglyMeasurable_mk.measurableSet_eq_fun hg.stronglyMeasurable_mk)).mpr
    filter_upwards [he,Measure.ae_ae_of_ae_prod hf.ae_eq_mk,Measure.ae_ae_of_ae_prod hg.ae_eq_mk]
      with a he hf hg
    filter_upwards [he,hf,hg] with b he hf hg
    exact hf.symm.trans (he.trans hg)
  exact hf.ae_eq_mk.trans (he'.trans hg.ae_eq_mk.symm)

@[expose] def driftProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N)
    (t : ℝ≥0) (ω : Parameter N p × Ω) : ℝ :=
  CutoffSDE.cutoffDrift β ω.1.1 R hR i (process D β R hR hJ T t ω)

@[expose] def noiseProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i j : Fin N)
    (t : ℝ≥0) (ω : Parameter N p × Ω) : ℝ :=
  CutoffSDE.cutoffNoise N R hR i j (process D β R hR hJ T t ω)

lemma cutoffDrift_evaluation_stronglyAdapted (β R : ℝ) (hR : 0 < R)
    (X : ℝ≥0 → Parameter N p × Ω → State N)
    (hX : StronglyAdapted (filtration (Parameter N p) F) X) (i : Fin N) :
    StronglyAdapted (filtration (Parameter N p) F)
      (fun t ω => CutoffSDE.cutoffDrift β ω.1.1 R hR i (X t ω)) := by
  intro t
  have hc : Continuous (fun q : FiniteModel.Disorder N p × State N => CutoffSDE.cutoffDrift β q.1 R hR i q.2) :=
    (CutoffSDE.coordinate_lipschitz i).continuous.comp
      (HamiltonianParameter.cutoffDrift_joint_continuous (N := N) (p := p) β R hR)
  have hp : StronglyMeasurable[filtration (Parameter N p) F t]
      (fun ω : Parameter N p × Ω => (ω.1.1,X t ω)) :=
    (((continuous_fst : Continuous (Prod.fst : Parameter N p → FiniteModel.Disorder N p)).stronglyMeasurable.comp_measurable
      (background_known t)).prodMk (hX t))
  convert hc.comp_stronglyMeasurable hp using 1

lemma driftProcess_stronglyAdapted (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    StronglyAdapted (filtration (Parameter N p) F) (driftProcess D β R hR hJ T i) :=
  cutoffDrift_evaluation_stronglyAdapted β R hR _ (process_stronglyAdapted D β R hR hJ T) i

lemma cutoffDrift_evaluation_continuous (β R : ℝ) (hR : 0 < R)
    (X : ℝ≥0 → Parameter N p × Ω → State N)
    (hX : ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => X t ω)) (i : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => CutoffSDE.cutoffDrift β ω.1.1 R hR i (X t ω)) := by
  filter_upwards [hX] with ω hc
  have hd : Continuous (fun q : FiniteModel.Disorder N p × State N => CutoffSDE.cutoffDrift β q.1 R hR i q.2) :=
    (CutoffSDE.coordinate_lipschitz i).continuous.comp
      (HamiltonianParameter.cutoffDrift_joint_continuous (N := N) (p := p) β R hR)
  have hp : Continuous (fun t => (ω.1.1,X t ω)) := continuous_const.prodMk hc
  exact hd.comp hp

lemma driftProcess_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => driftProcess D β R hR hJ T i t ω) := by
  exact cutoffDrift_evaluation_continuous β R hR _ (process_continuous D β R hR hJ T) i

lemma noiseProcess_stronglyAdapted (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i j : Fin N) :
    StronglyAdapted (filtration (Parameter N p) F) (noiseProcess D β R hR hJ T i j) := by
  intro t
  exact (noise_family_lipschitz N R hR i j).continuous.comp_stronglyMeasurable
    (process_stronglyAdapted D β R hR hJ T t)

lemma noiseProcess_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i j : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => noiseProcess D β R hR hJ T i j t ω) := by
  filter_upwards [process_continuous D β R hR hJ T] with ω hc
  exact (noise_family_lipschitz N R hR i j).continuous.comp hc

/-- The true coefficient class of a canonical state class is its actual
evaluated coefficient, with the precise finite-horizon time cut. -/
lemma predictableCoefficient_ae_actual {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} (T : ℝ≥0)
    (hX : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun z => X z.1 z.2)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) :
    (predictableCoefficient hg U T : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t ω => g (X t ω)) T := by
  filter_upwards [predictableCoefficient_coeFn hg U T,hX] with z hg hz
  rw [hg]
  by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [indicator_of_mem (show z ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] at hz
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht]
    exact congrArg g hz.symm
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right ht]

/-- Actual enlarged drift class equals evaluation of the random-disorder
cutoff drift on the constructed process. -/
theorem driftLift_coe (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    (driftLift D β R hR hJ T i : TimeProcessL2 (ρ.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      FourPapersCommon.continuousAdaptedTimeCut (driftProcess D β R hR hJ T i) T := by
  let V := driftLift D β R hR hJ T i
  let H := FourPapersCommon.continuousAdaptedTimeCut (driftProcess D β R hR hJ T i) T
  have hHa : AEStronglyMeasurable H (nonnegativeLebesgueMeasure.prod (ρ.prod P)) :=
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut (filtration (Parameter N p) F) _
      (driftProcess_stronglyAdapted D β R hR hJ T i) (driftProcess_continuous D β R hR hJ T i) T).mono
        (predictable_le_prod _)
  have he : (fun z : Parameter N p × (ℝ≥0 × Ω) => (V : TimeProcessL2 (ρ.prod P))
      (ParameterizedItoLift.unshuffle z)) =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)]
      H ∘ ParameterizedItoLift.unshuffle := by
    apply ae_eq_of_ae_sections
      ((Lp.aestronglyMeasurable (V : TimeProcessL2 (ρ.prod P))).comp_quasiMeasurePreserving
        (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
      (hHa.comp_quasiMeasurePreserving (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
    filter_upwards [ParameterizedItoLift.predictableFamily_slice_ae (driftFamily D β R hR hJ T i),
      (driftClass_memLp D β R hR T i hJ).coeFn_toLp,process_slice_allTimes D β R hR hJ T] with q hv hf hx
    have hcan := predictableCoefficient_ae_actual
      (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩) i) T
      (GlobalSDE.horizonProcess_timeCut D
        (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
        (noise_family_lipschitz N R hR) q.2 T)
    have hxt := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hx
    filter_upwards [hv,hcan,hxt] with z hv hcan hx
    have hv' : (V : TimeProcessL2 (ρ.prod P)) (z.1,(q,z.2)) =
        (driftClass D β R hR T i q : TimeProcessL2 P) z :=
      hv.trans (congrArg (fun U : PredictableProcessL2 F P => (U : TimeProcessL2 P) z) hf)
    exact hv'.trans (hcan.trans (by
      simp only [H,driftProcess,ParameterizedItoLift.unshuffle,Function.comp_def,
        FourPapersCommon.continuousAdaptedTimeCut,hx z.1]
      rfl))
  have hb := (PredictableFamilyLift.shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp he
  exact hb

/-- Actual enlarged matrix-noise class equals evaluation of the cutoff
projection coefficient on the constructed annealed process. -/
theorem noiseLift_coe (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i j : Fin N) :
    (noiseLift (p := p) (ρ := ρ) D β R hR T i j : TimeProcessL2 (ρ.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      FourPapersCommon.continuousAdaptedTimeCut (noiseProcess D β R hR hJ T i j) T := by
  let V := noiseLift (p := p) (ρ := ρ) D β R hR T i j
  let H := FourPapersCommon.continuousAdaptedTimeCut (noiseProcess D β R hR hJ T i j) T
  have hHa : AEStronglyMeasurable H (nonnegativeLebesgueMeasure.prod (ρ.prod P)) :=
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut (filtration (Parameter N p) F) _
      (noiseProcess_stronglyAdapted D β R hR hJ T i j) (noiseProcess_continuous D β R hR hJ T i j) T).mono
        (predictable_le_prod _)
  have he : (fun z : Parameter N p × (ℝ≥0 × Ω) => (V : TimeProcessL2 (ρ.prod P))
      (ParameterizedItoLift.unshuffle z)) =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)]
      H ∘ ParameterizedItoLift.unshuffle := by
    apply ae_eq_of_ae_sections
      ((Lp.aestronglyMeasurable (V : TimeProcessL2 (ρ.prod P))).comp_quasiMeasurePreserving
        (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
      (hHa.comp_quasiMeasurePreserving (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
    filter_upwards [ParameterizedItoLift.predictableFamily_slice_ae (noiseFamily (p := p) (ρ := ρ) D β R hR T i j),
      (noiseClass_memLp (ρ := ρ) D β R hR T i j).coeFn_toLp,process_slice_allTimes D β R hR hJ T] with q hv hf hx
    have hcan := predictableCoefficient_ae_actual
      (noise_family_lipschitz N R hR i j) T
      (GlobalSDE.horizonProcess_timeCut D
        (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
        (noise_family_lipschitz N R hR) q.2 T)
    have hxt := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hx
    filter_upwards [hv,hcan,hxt] with z hv hcan hx
    have hv' : (V : TimeProcessL2 (ρ.prod P)) (z.1,(q,z.2)) =
        (noiseClass D β R hR T i j q : TimeProcessL2 P) z :=
      hv.trans (congrArg (fun U : PredictableProcessL2 F P => (U : TimeProcessL2 P) z) hf)
    exact hv'.trans (hcan.trans (by
      simp only [H,noiseProcess,ParameterizedItoLift.unshuffle,Function.comp_def,
        FourPapersCommon.continuousAdaptedTimeCut,hx z.1]
      rfl))
  have hb := (PredictableFamilyLift.shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp he
  exact hb

end SphericalAging.AnnealedCutoffCoefficients
