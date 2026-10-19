module

public import SphericalAging.HardSphereDynamics
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Probability.Independence.Basic

public section

/-! A genuine null augmentation of the complete driving filtration.
The ambient measure is unchanged. Its augmented events are ambient measurable
and equal almost surely to events in the original filtration, so the actual
joint Brownian increment independence is preserved. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.NullAugmentation
variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Add all ambient-measurable null events, without assuming usual conditions
or changing the underlying probability measure. -/
@[expose] def augment (F : Filtration ℝ≥0 m) (P : Measure Ω) : Filtration ℝ≥0 m where
  seq t := m ⊓ eventuallyMeasurableSpace (F t) (ae P)
  mono' := by
    intro s t hst
    apply inf_le_inf_left
    intro A hA
    rcases hA with ⟨B, hB, hAB⟩
    exact ⟨B, F.mono hst _ hB, hAB⟩
  le' _ := inf_le_left

theorem le_augment (F : Filtration ℝ≥0 m) (t : ℝ≥0) : F t ≤ augment F P t :=
  le_inf (F.le t) le_eventuallyMeasurableSpace

theorem augment_event_ae (F : Filtration ℝ≥0 m) (t : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[augment F P t] A) :
    ∃ B : Set Ω, MeasurableSet[F t] B ∧ A =ᵐ[P] B := hA.2

theorem null_measurable_augment (F : Filtration ℝ≥0 m) (t : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet A) (hzero : P A = 0) : MeasurableSet[augment F P t] A := by
  have heq : A =ᵐ[P] (∅ : Set Ω) := ae_eq_empty.mpr hzero
  have he : MeasurableSet[F t] (∅ : Set Ω) := @MeasurableSet.empty Ω (F t)
  exact ⟨hA, ∅, he, heq⟩

/-- Actual independent increments stay independent of the augmented past. -/
theorem indep_augment (F : Filtration ℝ≥0 m) (t : ℝ≥0)
    {G : MeasurableSpace Ω} (hG : G ≤ m) (h : Indep (_mΩ := m) G (F t) P) :
    Indep (_mΩ := m) G (augment (m := m) F P t) P := by
  letI : MeasurableSpace Ω := m
  apply (indep_iff_forall_indepSet (m₁ := G) (m₂ := augment F P t) (_mΩ := m) P).2
  intro A C hA hC
  obtain ⟨B, hB, hCB⟩ := augment_event_ae (m := m) (P := P) F t hC
  have hold := @Indep.indepSet_of_measurableSet Ω G (F t) m P h A B hA hB
  apply (indepSet_iff_measure_inter_eq_mul (_mΩ := m) (hG _ hA) ((augment F P).le t _ hC) P).2
  have hACB : A ∩ C =ᵐ[P] A ∩ B := by
    filter_upwards [hCB] with omega homega
    exact congrArg (fun Q : Prop => omega ∈ A ∧ Q) homega
  rw [measure_congr hACB, measure_congr hCB]
  exact (indepSet_iff_measure_inter_eq_mul (_mΩ := m) (hG _ hA) (F.le t _ hB) P).1 hold

/-- The augmented driver retains the actual Brownian laws, independent
coordinate paths, and independence of the whole vector increment from the
full augmented filtration. -/
@[expose] def driver {N : ℕ} {F : Filtration ℝ≥0 m}
    (D : HardSphereDynamics.BrownianDriver N P F) :
    HardSphereDynamics.BrownianDriver N P (augment F P) where
  coordinate := D.coordinate
  brownian := D.brownian
  independent := D.independent
  filtered i :=
    { toIsPreBrownianReal := (D.filtered i).toIsPreBrownianReal
      stronglyAdapted := fun t => ((D.filtered i).stronglyAdapted t).mono (le_augment F t)
      indep := fun s t hst => indep_augment F s
        (Measurable.comap_le ((D.coordinateStronglyMeasurable i t).measurable.sub
          (D.coordinateStronglyMeasurable i s).measurable)) ((D.filtered i).indep s t hst) }
  jointFiltered s t hst := by
    apply indep_augment F s _ (D.jointFiltered s t hst)
    apply Measurable.comap_le
    exact measurable_pi_lambda (fun i =>
      (D.coordinateStronglyMeasurable i t).measurable.sub (D.coordinateStronglyMeasurable i s).measurable)

/-- Any measurable null event is known already at time zero in the augmented
filtration. This is sufficient to select all-path continuous versions. -/
theorem augment_null_known_zero (F : Filtration ℝ≥0 m) {A : Set Ω}
    (hA : MeasurableSet A) (hzero : P A = 0) : MeasurableSet[augment F P 0] A :=
  null_measurable_augment F 0 hA hzero

/-- Remove the exceptional null set of paths, preserving adaptation in any
filtration that already contains ambient null events at time zero. The
augmentation above proves that premise for the actual Brownian model. -/
theorem exists_allPath_continuous_modification {E : Type*} [TopologicalSpace E] [Zero E]
    (F : Filtration ℝ≥0 m)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (X : ℝ≥0 → Ω → E) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega)) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted F Y ∧
      (∀ omega, Continuous (fun t => Y t omega)) ∧ (∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega) := by
  classical
  have hbad : P {omega | ¬ Continuous (fun t => X t omega)} = 0 := by
    simpa only [ae_iff] using hXc
  obtain ⟨A, hsub, hAm, hA0⟩ := exists_measurable_superset_of_null hbad
  let Y : ℝ≥0 → Ω → E := fun t omega => if omega ∈ A then 0 else X t omega
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro t
    change StronglyMeasurable[F t] (A.piecewise (fun _ => (0 : E)) (X t))
    exact stronglyMeasurable_const.piecewise (F.mono (zero_le : 0 ≤ t) _ (hnull A hAm hA0)) (hXa t)
  · intro omega
    by_cases homega : omega ∈ A
    · simpa only [Y, if_pos homega] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : E)))
    · have hc : Continuous (fun t => X t omega) := by
        by_contra hn
        exact homega (hsub hn)
      simpa only [Y, if_neg homega] using hc
  · have hae : ∀ᵐ omega ∂P, omega ∉ A := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using hA0
    filter_upwards [hae] with omega homega
    intro t
    simp only [Y, if_neg homega]

/-- All-path continuous adapted versions exist on the explicitly augmented
Brownian filtration, without a right-continuity assumption. -/
theorem exists_allPath_continuous_modification_augmented {E : Type*}
    [TopologicalSpace E] [Zero E] (F : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → E) (hXa : StronglyAdapted (augment F P) X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega)) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted (augment F P) Y ∧
      (∀ omega, Continuous (fun t => Y t omega)) ∧ (∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega) :=
  exists_allPath_continuous_modification (augment F P)
    (fun _ hA hzero => augment_null_known_zero F hA hzero) X hXa hXc

end SphericalAging.NullAugmentation
