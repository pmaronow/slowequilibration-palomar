module

public import BrownianMotion.Gaussian.BrownianMotion
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import SphericalAging.HardSphereDynamics

public section

/-!
# Actual independent Brownian coordinate drivers

The probability space is a finite product of continuous path spaces. The
filtration records every coordinate up to the current time. Increment
independence from this complete vector past is proved from scalar Brownian
independence and product measures, rather than assumed as driving data.
-/

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Filtration Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology

namespace SphericalAging.VectorBrownian

@[expose] abbrev Path := C(ℝ≥0, ℝ)

@[expose] def scalarPath (ω : ℝ≥0 → ℝ) : Path :=
  ⟨fun t => brownian t ω, continuous_brownian ω⟩

lemma scalarPath_measurable : Measurable scalarPath := by
  rw [ContinuousMap.measurable_iff_eval]
  exact measurable_brownian

/-- The continuous Brownian path law constructed in the staged foundations. -/
@[expose] def pathLaw : Measure Path := gaussianLimit.map scalarPath

lemma pathLaw_eq_wienerMeasure : pathLaw = wienerMeasure := by
  have hm : Measurable (fun ω : ℝ≥0 → ℝ =>
      (⟨fun t => brownian t ω, continuous_brownian ω⟩ :
        {f : ℝ≥0 → ℝ // Continuous f})) := by
    apply Measurable.subtype_mk
    exact measurable_pi_iff.mpr measurable_brownian
  unfold pathLaw wienerMeasure wienerMeasureAux
  rw [Measure.map_map MeasurableEquiv.continuousMap.measurable hm]
  rfl

lemma scalarPath_hasLaw : HasLaw scalarPath pathLaw gaussianLimit :=
  hasLaw_map scalarPath_measurable.aemeasurable

instance pathLaw_probability : IsProbabilityMeasure pathLaw :=
  scalarPath_hasLaw.isProbabilityMeasure_iff.mp inferInstance

lemma scalar_eval_measurable (t : ℝ≥0) : Measurable (fun ω : Path => ω t) :=
  (by fun_prop : Continuous (fun ω : Path => ω t)).measurable

lemma scalar_isPreBrownian : IsPreBrownianReal (fun t (ω : Path) => ω t) pathLaw where
  hasLaw I := by
    have hm : Measurable (fun ω : Path => I.restrict (fun t => ω t)) := by
      exact measurable_pi_iff.mpr (fun t => scalar_eval_measurable t)
    exact HasLaw.comp_of_hasLaw_comp (f := fun ω : Path => I.restrict (fun t => ω t))
      hm.aemeasurable scalarPath_hasLaw (HasLaw.id (μ := pathLaw))
      (isBrownianReal_brownian.hasLaw I)

lemma scalar_isBrownian : IsBrownianReal (fun t (ω : Path) => ω t) pathLaw where
  toIsPreBrownianReal := scalar_isPreBrownian
  cont := Eventually.of_forall (fun ω => ω.continuous)

@[expose] abbrev Space (N : ℕ) := Fin N → Path

@[expose] def law (N : ℕ) : Measure (Space N) := Measure.pi (fun _ => pathLaw)

instance law_probability (N : ℕ) : IsProbabilityMeasure (law N) := by
  unfold law
  infer_instance

@[expose] def coordinate {N : ℕ} (i : Fin N) (t : ℝ≥0) (ω : Space N) : ℝ := ω i t

@[expose] def process {N : ℕ} (t : ℝ≥0) (ω : Space N) : Fin N → ℝ := fun i => coordinate i t ω

lemma coordinate_measurable {N : ℕ} (i : Fin N) (t : ℝ≥0) :
    Measurable (coordinate i t) := (scalar_eval_measurable t).comp (measurable_pi_apply i)

lemma process_measurable (N : ℕ) (t : ℝ≥0) : Measurable (process (N := N) t) :=
  measurable_pi_iff.mpr (fun i => coordinate_measurable i t)

/-- Every coordinate history is observed by this filtration. -/
@[expose] def filtration (N : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Space N)) :=
  natural process (fun t => (process_measurable N t).stronglyMeasurable)

lemma coordinate_isPreBrownian {N : ℕ} (i : Fin N) :
    IsPreBrownianReal (coordinate i) (law N) where
  hasLaw I := (scalar_isPreBrownian.hasLaw I).comp
    (measurePreserving_eval (fun _ : Fin N => pathLaw) i).hasLaw

lemma coordinate_isBrownian {N : ℕ} (i : Fin N) :
    IsBrownianReal (coordinate i) (law N) where
  toIsPreBrownianReal := coordinate_isPreBrownian i
  cont := Eventually.of_forall (fun ω => (ω i).continuous)

lemma paths_independent (N : ℕ) :
    iIndepFun (fun i (ω : Space N) => fun t => coordinate i t ω) (law N) := by
  exact iIndepFun_pi (fun _ => (measurable_pi_iff.mpr scalar_eval_measurable).aemeasurable)

lemma coordinate_stronglyAdapted {N : ℕ} (i : Fin N) :
    StronglyAdapted (filtration N) (coordinate i) := by
  intro t
  have h := stronglyAdapted_natural (fun s => (process_measurable N s).stronglyMeasurable) t
  exact ((measurable_pi_apply i).comp h.measurable).stronglyMeasurable

/-- The complete scalar past and a subsequent increment are independent. -/
lemma scalar_increment_indep_past {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω : Path => ω t - ω s) (fun (ω : Path) (u : Iic s) => ω u) pathLaw := by
  have h := scalar_isPreBrownian.indepFun_shift s
  have hh := h.comp (measurable_pi_apply (t - s)) measurable_id
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hh

/-- Tensorization of independence: independent pairs in each coordinate give
independent first and second vectors on the finite product probability space. -/
lemma product_vectors_independent {ι Ω A B : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ι → Ω → A) (Y : ι → Ω → B)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXY : ∀ i, IndepFun (X i) (Y i) (μ i)) :
    IndepFun (fun ω i => X i (ω i)) (fun ω i => Y i (ω i)) (Measure.pi μ) := by
  let ν : ι → Measure A := fun i => (μ i).map (X i)
  let ξ : ι → Measure B := fun i => (μ i).map (Y i)
  have hν : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (hasLaw_map (hX i).aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hξ : ∀ i, IsProbabilityMeasure (ξ i) := fun i =>
    (hasLaw_map (hY i).aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hpair : ∀ i, IsProbabilityMeasure ((μ i).map (fun ω => (X i ω, Y i ω))) := fun i =>
    (hasLaw_map ((hX i).prodMk (hY i)).aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hVX : Measurable (fun (ω : ι → Ω) i => X i (ω i)) :=
    measurable_pi_iff.mpr (fun i => (hX i).comp (measurable_pi_apply i))
  have hVY : Measurable (fun (ω : ι → Ω) i => Y i (ω i)) :=
    measurable_pi_iff.mpr (fun i => (hY i).comp (measurable_pi_apply i))
  have hVP : Measurable (fun (ω : ι → Ω) i => (X i (ω i), Y i (ω i))) :=
    measurable_pi_iff.mpr (fun i => ((hX i).prodMk (hY i)).comp (measurable_pi_apply i))
  have hpairs : (Measure.pi μ).map (fun ω i => (X i (ω i), Y i (ω i))) =
      Measure.pi (fun i => (ν i).prod (ξ i)) := by
    rw [Measure.pi_map_pi (fun i => ((hX i).prodMk (hY i)).aemeasurable)]
    congr 1
    funext i
    exact (hXY i).map_prod_eq_prod_map_map (hX i).aemeasurable (hY i).aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map hVX.aemeasurable hVY.aemeasurable,
    Measure.pi_map_pi (fun i => (hX i).aemeasurable),
    Measure.pi_map_pi (fun i => (hY i).aemeasurable)]
  calc
    _ = ((Measure.pi μ).map (fun ω i => (X i (ω i), Y i (ω i)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow A B ι) := by
      rw [Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow A B ι).measurable hVP]
      rfl
    _ = (Measure.pi (fun i => (ν i).prod (ξ i))).map
        (MeasurableEquiv.arrowProdEquivProdArrow A B ι) := by rw [hpairs]
    _ = (Measure.pi ν).prod (Measure.pi ξ) :=
      (measurePreserving_arrowProdEquivProdArrow A B ι ν ξ).map_eq

lemma vector_increment_indep_past {N : ℕ} {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun (ω : Space N) i => coordinate i t ω - coordinate i s ω)
      (fun (ω : Space N) (i : Fin N) (u : Iic s) => coordinate i u ω) (law N) := by
  apply product_vectors_independent (fun _ : Fin N => pathLaw)
    (fun _ (ω : Path) => ω t - ω s) (fun _ (ω : Path) (u : Iic s) => ω u)
  · intro i
    exact (scalar_eval_measurable t).sub (scalar_eval_measurable s)
  · intro i
    exact measurable_pi_iff.mpr (fun u => scalar_eval_measurable u)
  · intro i
    exact scalar_increment_indep_past hst

/-- Each coordinate's increment is independent of the entire vector history. -/
lemma coordinate_increment_indep_past {N : ℕ} (i : Fin N) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun (ω : Space N) => coordinate i t ω - coordinate i s ω)
      (fun (ω : Space N) (u : Iic s) j => coordinate j u ω) (law N) := by
  have h := vector_increment_indep_past (N := N) hst
  have htranspose : Measurable (fun (f : Fin N → Iic s → ℝ) (u : Iic s) j => f j u) := by
    exact measurable_pi_iff.mpr (fun u => measurable_pi_iff.mpr
      (fun j => (measurable_pi_apply u).comp (measurable_pi_apply j)))
  exact h.comp (measurable_pi_apply i) htranspose

lemma vector_increment_indep_filtration {N : ℕ} {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun (ω : Space N) i =>
        coordinate i t ω - coordinate i s ω) inferInstance) (filtration N s) (law N) := by
  have htranspose : Measurable (fun (f : Fin N → Iic s → ℝ) (u : Iic s) j => f j u) :=
    measurable_pi_iff.mpr (fun u => measurable_pi_iff.mpr
      (fun j => (measurable_pi_apply u).comp (measurable_pi_apply j)))
  have h := (vector_increment_indep_past (N := N) hst).comp measurable_id htranspose
  rw [filtration, natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).1 h

lemma coordinate_isFilteredPreBrownian {N : ℕ} (i : Fin N) :
    IsFilteredPreBrownian (coordinate i) (filtration N) (law N) where
  toIsPreBrownianReal := coordinate_isPreBrownian i
  stronglyAdapted := coordinate_stronglyAdapted i
  indep s t hst := by
    have h := (IndepFun_iff_Indep _ _ _).1 (coordinate_increment_indep_past i hst)
    rw [filtration, natural_eq_comap]
    exact h

/-- Concrete independent N-dimensional Brownian driving data in its complete
vector natural filtration. This inhabits the interface used by the SDE. -/
@[expose] def driver (N : ℕ) : HardSphereDynamics.BrownianDriver N (law N) (filtration N) where
  coordinate := coordinate
  brownian := coordinate_isBrownian
  filtered := coordinate_isFilteredPreBrownian
  independent := paths_independent N
  jointFiltered := fun _s _t hst => vector_increment_indep_filtration hst

/-- Actual existence, with the probability space and its law explicitly supplied. -/
theorem independent_filtered_brownian_exists (N : ℕ) :
    Nonempty (HardSphereDynamics.BrownianDriver N (law N) (filtration N)) := ⟨driver N⟩

/-- An independent background can be revealed at time zero without changing
increment independence: a future variable remains independent of background
and the old past jointly. -/
lemma independent_background_and_past {A Ω X Y : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure A) (μ : Measure Ω) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (f : Ω → X) (g : Ω → Y) (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g μ) :
    IndepFun (fun ω : A × Ω => f ω.2) (fun ω : A × Ω => (ω.1, g ω.2)) (ρ.prod μ) := by
  let ν := μ.map f
  let ξ := μ.map g
  have hν : IsProbabilityMeasure ν := (hasLaw_map hf.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hξ : IsProbabilityMeasure ξ := (hasLaw_map hg.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hbase : HasLaw (fun ω : A × Ω => (ω.1, (f ω.2, g ω.2)))
      (ρ.prod (ν.prod ξ)) (ρ.prod μ) := by
    refine ⟨(measurable_fst.prodMk ((hf.comp measurable_snd).prodMk
      (hg.comp measurable_snd))).aemeasurable, ?_⟩
    have heq := Measure.map_prod_map ρ μ measurable_id (hf.prodMk hg)
    rw [Measure.map_id, hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at heq
    exact heq.symm
  have hshuffle : MeasurePreserving (fun ω : A × X × Y => (ω.2.1, (ω.1, ω.2.2)))
      (ρ.prod (ν.prod ξ)) (ν.prod (ρ.prod ξ)) := by
    have hi := MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ρ ν ξ)
    have hs : MeasurePreserving (Prod.swap : A × X → X × A) (ρ.prod ν) (ν.prod ρ) :=
      Measure.measurePreserving_swap
    have hp := hs.prod ((HasLaw.id (μ := ξ)).measurePreserving measurable_id)
    exact (measurePreserving_prodAssoc ν ρ ξ).comp (hp.comp hi)
  have hjoint : HasLaw (fun ω : A × Ω => (f ω.2, (ω.1, g ω.2)))
      (ν.prod (ρ.prod ξ)) (ρ.prod μ) := hshuffle.hasLaw.comp hbase
  have hfirst : HasLaw (fun ω : A × Ω => f ω.2) ν (ρ.prod μ) :=
    measurePreserving_fst.hasLaw.comp hjoint
  have hsecond : HasLaw (fun ω : A × Ω => (ω.1, g ω.2)) (ρ.prod ξ) (ρ.prod μ) :=
    measurePreserving_snd.hasLaw.comp hjoint
  exact (indepFun_iff_map_prod_eq_prod_map_map hfirst.aemeasurable hsecond.aemeasurable).2
    (by rw [hjoint.map_eq, hfirst.map_eq, hsecond.map_eq])

section Background

variable {A : Type*} [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]

@[expose] abbrev BackgroundSpace (A : Type*) (N : ℕ) := A × Space N

@[expose] def backgroundLaw (ρ : Measure A) (N : ℕ) : Measure (BackgroundSpace A N) := ρ.prod (law N)

instance backgroundLaw_probability (ρ : Measure A) [IsProbabilityMeasure ρ] (N : ℕ) :
    IsProbabilityMeasure (backgroundLaw ρ N) := by unfold backgroundLaw; infer_instance

@[expose] def backgroundCoordinate {N : ℕ} (i : Fin N) (t : ℝ≥0) (ω : BackgroundSpace A N) : ℝ :=
  coordinate i t ω.2

@[expose] def backgroundProcess {N : ℕ} (t : ℝ≥0) (ω : BackgroundSpace A N) : A × (Fin N → ℝ) :=
  (ω.1, process t ω.2)

omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma backgroundProcess_measurable (N : ℕ) (t : ℝ≥0) :
    Measurable (backgroundProcess (A := A) (N := N) t) :=
  measurable_fst.prodMk ((process_measurable N t).comp measurable_snd)

/-- The independent initial point and disorder are known at time zero;
all coordinate Brownian histories are observed at subsequent times. -/
@[expose] def backgroundFiltration (A : Type*) [TopologicalSpace A] [MetrizableSpace A]
    [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (N : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (BackgroundSpace A N)) :=
  natural backgroundProcess (fun t => (backgroundProcess_measurable N t).stronglyMeasurable)

omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma background_coordinate_isBrownian {N : ℕ} (ρ : Measure A) [IsProbabilityMeasure ρ]
    (i : Fin N) : IsBrownianReal (backgroundCoordinate (A := A) i) (backgroundLaw ρ N) where
  toIsPreBrownianReal := {
    hasLaw := fun I => ((coordinate_isPreBrownian i).hasLaw I).comp measurePreserving_snd.hasLaw }
  cont := Eventually.of_forall (fun ω => (ω.2 i).continuous)

lemma background_coordinate_stronglyAdapted {N : ℕ} (i : Fin N) :
    StronglyAdapted (backgroundFiltration A N) (backgroundCoordinate i) := by
  intro t
  have h := stronglyAdapted_natural
    (fun s => (backgroundProcess_measurable (A := A) N s).stronglyMeasurable) t
  exact ((measurable_pi_apply i).comp (measurable_snd.comp h.measurable)).stronglyMeasurable

lemma background_known_at_zero {N : ℕ} :
    StronglyMeasurable[backgroundFiltration A N 0] (Prod.fst : BackgroundSpace A N → A) := by
  have h := stronglyAdapted_natural
    (fun s => (backgroundProcess_measurable (A := A) N s).stronglyMeasurable) 0
  exact (measurable_fst.comp h.measurable).stronglyMeasurable

omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma background_coordinate_increment_indep_past {N : ℕ} (ρ : Measure A)
    [IsProbabilityMeasure ρ] (i : Fin N) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω : BackgroundSpace A N => backgroundCoordinate i t ω - backgroundCoordinate i s ω)
      (fun (ω : BackgroundSpace A N) (u : Iic s) => backgroundProcess u ω) (backgroundLaw ρ N) := by
  have hp : Measurable (fun (ω : Space N) (u : Iic s) j => coordinate j u ω) :=
    measurable_pi_iff.mpr (fun u => process_measurable N u)
  have h := independent_background_and_past ρ (law N)
    (fun ω : Space N => coordinate i t ω - coordinate i s ω)
    (fun (ω : Space N) (u : Iic s) j => coordinate j u ω)
    ((coordinate_measurable i t).sub (coordinate_measurable i s)) hp
    (coordinate_increment_indep_past i hst)
  have hm : Measurable (fun (f : A × (Iic s → Fin N → ℝ)) (u : Iic s) => (f.1, f.2 u)) :=
    measurable_pi_iff.mpr (fun u => measurable_fst.prodMk
      ((measurable_pi_apply u).comp measurable_snd))
  exact h.comp measurable_id hm

/- Joint increment independence is stronger than separate coordinate
independence and supplies the cross-coordinate stochastic integration bounds. -/
omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma background_vector_increment_indep_past {N : ℕ} (ρ : Measure A)
    [IsProbabilityMeasure ρ] {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun (ω : BackgroundSpace A N) i =>
      backgroundCoordinate i t ω - backgroundCoordinate i s ω)
      (fun (ω : BackgroundSpace A N) (u : Iic s) => backgroundProcess u ω) (backgroundLaw ρ N) := by
  have hinc : Measurable (fun (ω : Space N) i => coordinate i t ω - coordinate i s ω) :=
    measurable_pi_iff.mpr (fun i => (coordinate_measurable i t).sub (coordinate_measurable i s))
  have hp : Measurable (fun (ω : Space N) (i : Fin N) (u : Iic s) => coordinate i u ω) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun u => coordinate_measurable i u))
  have h := independent_background_and_past ρ (law N)
    (fun (ω : Space N) i => coordinate i t ω - coordinate i s ω)
    (fun (ω : Space N) (i : Fin N) (u : Iic s) => coordinate i u ω)
    hinc hp (vector_increment_indep_past hst)
  have hm : Measurable (fun (f : A × (Fin N → Iic s → ℝ)) (u : Iic s) =>
      (f.1, fun i => f.2 i u)) := by
    exact measurable_pi_iff.mpr (fun u => measurable_fst.prodMk
      (measurable_pi_iff.mpr (fun i => (measurable_pi_apply u).comp
        ((measurable_pi_apply i).comp measurable_snd))))
  exact h.comp measurable_id hm

lemma background_vector_increment_indep_filtration {N : ℕ} (ρ : Measure A)
    [IsProbabilityMeasure ρ] {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun (ω : BackgroundSpace A N) i =>
        backgroundCoordinate i t ω - backgroundCoordinate i s ω) inferInstance)
      (backgroundFiltration A N s) (backgroundLaw ρ N) := by
  rw [backgroundFiltration, natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).1 (background_vector_increment_indep_past ρ hst)

lemma background_coordinate_isFilteredPreBrownian {N : ℕ} (ρ : Measure A)
    [IsProbabilityMeasure ρ] (i : Fin N) :
    IsFilteredPreBrownian (backgroundCoordinate i) (backgroundFiltration A N) (backgroundLaw ρ N) where
  toIsPreBrownianReal := (background_coordinate_isBrownian ρ i).toIsPreBrownianReal
  stronglyAdapted := background_coordinate_stronglyAdapted i
  indep s t hst := by
    have h := (IndepFun_iff_Indep _ _ _).1 (background_coordinate_increment_indep_past ρ i hst)
    rw [backgroundFiltration, natural_eq_comap]
    exact h

omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma background_paths_independent (ρ : Measure A) [IsProbabilityMeasure ρ] (N : ℕ) :
    iIndepFun (fun i (ω : BackgroundSpace A N) => fun t => backgroundCoordinate i t ω)
      (backgroundLaw ρ N) := by
  have hm : ∀ i : Fin N, Measurable (fun (ω : Space N) t => coordinate i t ω) :=
    fun i => measurable_pi_iff.mpr (fun t => coordinate_measurable i t)
  change iIndepFun (fun i => (fun (ω : Space N) t => coordinate i t ω) ∘
    (Prod.snd : BackgroundSpace A N → Space N)) (backgroundLaw ρ N)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).comp measurable_snd |>.aemeasurable)]
  have hs : (backgroundLaw ρ N).map (Prod.snd : BackgroundSpace A N → Space N) = law N :=
    measurePreserving_snd.map_eq
  have hmaps : ∀ i : Fin N, (backgroundLaw ρ N).map
      (fun (ω : BackgroundSpace A N) t => backgroundCoordinate i t ω) =
      (law N).map (fun (ω : Space N) t => coordinate i t ω) := by
    intro i
    change (backgroundLaw ρ N).map ((fun (ω : Space N) t => coordinate i t ω) ∘ Prod.snd) = _
    rw [← Measure.map_map (hm i) measurable_snd, hs]
  have hmvec : Measurable (fun (ω : Space N) i t => coordinate i t ω) :=
    measurable_pi_iff.mpr hm
  change (backgroundLaw ρ N).map ((fun (ω : Space N) i t => coordinate i t ω) ∘ Prod.snd) = _
  rw [← Measure.map_map hmvec measurable_snd, hs]
  change (law N).map (fun (ω : Space N) i t => coordinate i t ω) =
    Measure.pi (fun i => (backgroundLaw ρ N).map
      (fun (ω : BackgroundSpace A N) t => backgroundCoordinate i t ω))
  simp_rw [hmaps]
  exact (paths_independent N).map_fun_eq_pi_map (fun i => (hm i).aemeasurable)

/-- Actual N-coordinate drivers after revealing any independent background law
at zero, for example the initial point together with Gaussian disorder. -/
@[expose] def backgroundDriver (ρ : Measure A) [IsProbabilityMeasure ρ] (N : ℕ) :
    HardSphereDynamics.BrownianDriver N (backgroundLaw ρ N) (backgroundFiltration A N) where
  coordinate := backgroundCoordinate
  brownian := background_coordinate_isBrownian ρ
  filtered := background_coordinate_isFilteredPreBrownian ρ
  independent := background_paths_independent ρ N
  jointFiltered := fun _s _t hst => background_vector_increment_indep_filtration ρ hst

end Background

/-- The manuscript's initial point and actual ordered Gaussian tensor form
one independent background before taking its product with Brownian paths. -/
@[expose] abbrev ModelBackground (N p : ℕ) := FiniteModel.Vector N × FiniteModel.Disorder N p

@[expose] def modelBackgroundLaw {N : ℕ} (ν : Measure (FiniteModel.Vector N)) (p : ℕ) :
    Measure (ModelBackground N p) := ν.prod (FiniteModel.disorderLaw N p)

instance modelBackgroundLaw_probability {N : ℕ} (ν : Measure (FiniteModel.Vector N))
    [IsProbabilityMeasure ν] (p : ℕ) : IsProbabilityMeasure (modelBackgroundLaw ν p) := by
  unfold modelBackgroundLaw
  infer_instance

/-- Brownian drivers with an independently sampled initial point and the
proved Gaussian tensor law, all revealed in the driving filtration at zero. -/
@[expose] def modelDriver {N : ℕ} (ν : Measure (FiniteModel.Vector N)) [IsProbabilityMeasure ν] (p : ℕ) :
    HardSphereDynamics.BrownianDriver N (backgroundLaw (modelBackgroundLaw ν p) N)
      (backgroundFiltration (ModelBackground N p) N) := backgroundDriver (modelBackgroundLaw ν p) N

lemma model_initial_known_at_zero {N p : ℕ} :
    StronglyMeasurable[backgroundFiltration (ModelBackground N p) N 0]
      (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.1) :=
  (measurable_fst.comp background_known_at_zero.measurable).stronglyMeasurable

lemma model_disorder_known_at_zero {N p : ℕ} :
    StronglyMeasurable[backgroundFiltration (ModelBackground N p) N 0]
      (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.2) :=
  (measurable_snd.comp background_known_at_zero.measurable).stronglyMeasurable

lemma model_initial_hasLaw {N : ℕ} (ν : Measure (FiniteModel.Vector N))
    [IsProbabilityMeasure ν] (p : ℕ) :
    HasLaw (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.1) ν
      (backgroundLaw (modelBackgroundLaw ν p) N) :=
  measurePreserving_fst.hasLaw.comp measurePreserving_fst.hasLaw

lemma model_disorder_hasLaw {N : ℕ} (ν : Measure (FiniteModel.Vector N))
    [IsProbabilityMeasure ν] (p : ℕ) :
    HasLaw (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.2)
      (FiniteModel.disorderLaw N p) (backgroundLaw (modelBackgroundLaw ν p) N) :=
  measurePreserving_snd.hasLaw.comp measurePreserving_fst.hasLaw

end SphericalAging.VectorBrownian
