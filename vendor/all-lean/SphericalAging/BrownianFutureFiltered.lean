module

public import SphericalAging.BrownianFuturePath
public import SphericalAging.ShiftedBrownian
public import SphericalAging.IndependentBackgroundDriver

public section

/-! Filtered law of the actual waiting state paired with the entire future
Wiener path. Null augmentation is retained, and every future sample map
is genuinely measurable for the corresponding full filtrations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal
namespace SphericalAging.BrownianFutureFiltered
open VectorBrownian BrownianFuturePath
set_option maxHeartbeats 1400000

/-- Filtered measure-preserving maps remain filtered after null augmentation. -/
lemma measurable_augment {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : Filtration ℝ≥0 mA} {G : Filtration ℝ≥0 mB} {φ : A → B}
    (hφ : MeasurePreserving φ μ ν) (t : ℝ≥0) (hF : @Measurable A B (F t) (G t) φ) :
    @Measurable A B (NullAugmentation.augment F μ t) (NullAugmentation.augment G ν t) φ := by
  intro S hS
  refine ⟨hφ.measurable hS.1,?_⟩
  obtain ⟨B,hB,hSB⟩ := hS.2
  refine ⟨φ ⁻¹' B,hF hB,?_⟩
  exact hφ.quasiMeasurePreserving.ae hSB

/-- The unaugmented future path is measurable from the actual shifted
natural filtration to the original natural filtration. -/
lemma future_filtered {N : ℕ} (s t : ℝ≥0) :
    @Measurable (Space N) (Space N) (filtration N (s+t)) (filtration N t) (future s) := by
  have he : filtration N t = MeasurableSpace.comap
      (fun (ω : Space N) (u : Iic t) => process u ω) inferInstance :=
    Filtration.natural_eq_comap _ _ t
  rw [he,measurable_iff_comap_le,MeasurableSpace.comap_comp]
  letI : MeasurableSpace (Space N) := filtration N (s+t)
  apply Measurable.comap_le
  apply measurable_pi_iff.mpr
  intro u
  apply measurable_pi_iff.mpr
  intro i
  exact ((coordinate_stronglyAdapted i (s+u)).mono
    ((filtration N).mono (add_le_add_right u.2 s))).measurable.sub
      (((coordinate_stronglyAdapted i s).mono
        ((filtration N).mono (le_add_right le_rfl))).measurable)

/-- The literal Wiener future map retains the full null augmented filtrations. -/
lemma future_augmented_filtered {N : ℕ} (s t : ℝ≥0) :
    @Measurable (Space N) (Space N)
      (NullAugmentation.augment (filtration N) (law N) (s+t))
      (NullAugmentation.augment (filtration N) (law N) t) (future s) := by
  have h := measurable_augment (F := ShiftedBrownian.filtration (filtration N) s)
    (G := filtration N) (future_measurePreserving s) t (future_filtered s t)
  exact h

/-- The entire future path is independent of the actual null-augmented waiting sigma algebra. -/
theorem future_indep_augmented {N : ℕ} (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (future (N := N) s) inferInstance)
      (NullAugmentation.augment (filtration N) (law N) s) (law N) :=
  NullAugmentation.indep_augment (filtration N) s
    (future_measurable s).comap_le (future_indep_filtration s)

/-- A state genuinely observed at the waiting time is independent of the
entire future Wiener path. -/
theorem waiting_indep_future {A : Type*} [MeasurableSpace A] {N : ℕ}
    (s : ℝ≥0) (Z : Space N → A)
    (hZ : Measurable[NullAugmentation.augment (filtration N) (law N) s] Z) :
    IndepFun Z (future s) (law N) := by
  rw [IndepFun_iff_Indep]
  exact (indep_of_indep_of_le_right (future_indep_augmented s) hZ.comap_le).symm

/-- The waiting state and future Brownian path have their true product law. -/
theorem waiting_future_measurePreserving {A : Type*} [MeasurableSpace A] {N : ℕ}
    (s : ℝ≥0) (Z : Space N → A)
    (hZ : Measurable[NullAugmentation.augment (filtration N) (law N) s] Z) :
    MeasurePreserving (fun ω => (Z ω,future s ω)) (law N) (((law N).map Z).prod (law N)) := by
  have hm : Measurable Z := hZ.mono
    ((NullAugmentation.augment (filtration N) (law N)).le s) le_rfl
  refine ⟨hm.prodMk (future_measurable s),?_⟩
  rw [(waiting_indep_future s Z hZ).map_prod_eq_prod_map_map hm.aemeasurable
    (future_measurable s).aemeasurable,future_map]

/-- Pairing an observed waiting state with the future path is genuinely
filtered for the independent-background future filtration. -/
lemma waiting_future_filtered {A : Type*} [MeasurableSpace A] {N : ℕ}
    (s : ℝ≥0) (Z : Space N → A)
    (hZ : Measurable[NullAugmentation.augment (filtration N) (law N) s] Z) (t : ℝ≥0) :
    @Measurable (Space N) (A × Space N)
      (NullAugmentation.augment (filtration N) (law N) (s+t))
      (IndependentBackgroundDriver.filtration A
        (NullAugmentation.augment (filtration N) (law N)) t)
      (fun ω => (Z ω,future s ω)) := by
  exact (hZ.mono ((NullAugmentation.augment (filtration N) (law N)).mono
    (le_add_right le_rfl)) le_rfl).prodMk (future_augmented_filtered s t)

end SphericalAging.BrownianFutureFiltered
