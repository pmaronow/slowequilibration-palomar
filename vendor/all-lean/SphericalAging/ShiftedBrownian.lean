module

public import SphericalAging.VectorBrownian
public import SphericalAging.NullAugmentation

public section

/-! Actual Brownian drivers after a deterministic waiting time.
The shifted filtration retains the entire original history at the waiting
 time, including independent background disorder and the initial point.
Every Brownian and vector-increment property is proved from the original
actual driver. No shifted driving law is an additional hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedBrownian
open HardSphereDynamics
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The full original past at time `s+t`. -/
@[expose] def filtration (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (s : ℝ≥0) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := F (s+t)
  mono' := fun _ _ h => F.mono (add_le_add le_rfl h)
  le' := fun t => F.le (s+t)

@[simp] lemma filtration_apply (s t : ℝ≥0) : filtration F s t=F (s+t) := rfl
@[simp] lemma filtration_zero (s : ℝ≥0) : filtration F s 0=F s := by simp

/-- The actual centered future increment of an original Brownian coordinate. -/
@[expose] def coordinate (D : BrownianDriver N P F) (s : ℝ≥0) (i : Fin N)
    (t : ℝ≥0) (omega : Ω) : ℝ := D.coordinate i (s+t) omega-D.coordinate i s omega

@[simp] lemma coordinate_zero (D : BrownianDriver N P F) (s : ℝ≥0) (i : Fin N)
    (omega : Ω) : coordinate D s i 0 omega=0 := by simp [coordinate]

lemma coordinate_increment (D : BrownianDriver N P F) (s u t : ℝ≥0) (i : Fin N)
    (omega : Ω) : coordinate D s i t omega-coordinate D s i u omega=
      D.coordinate i (s+t) omega-D.coordinate i (s+u) omega := by
  simp only [coordinate]
  ring

lemma coordinate_brownian (D : BrownianDriver N P F) (s : ℝ≥0) (i : Fin N) :
    IsBrownianMotion (coordinate D s i) P := (D.brownian i).shift s

lemma coordinate_adapted (D : BrownianDriver N P F) (s : ℝ≥0) (i : Fin N) :
    StronglyAdapted (filtration F s) (coordinate D s i) := by
  intro t
  exact ((D.filtered i).stronglyAdapted (s+t)).sub
    (((D.filtered i).stronglyAdapted s).mono (F.mono (le_add_right le_rfl)))

lemma coordinate_filtered (D : BrownianDriver N P F) (s : ℝ≥0) (i : Fin N) :
    IsFilteredPreBrownian (coordinate D s i) (filtration F s) P where
  toIsPreBrownianReal := (coordinate_brownian D s i).toIsPreBrownianReal
  stronglyAdapted := coordinate_adapted D s i
  indep u t hut := by
    have he : coordinate D s i t-coordinate D s i u=
        D.coordinate i (s+t)-D.coordinate i (s+u) := by
      funext omega
      exact coordinate_increment D s u t i omega
    rw [he]
    exact (D.filtered i).indep (s+u) (s+t) (add_le_add le_rfl hut)

lemma paths_independent (D : BrownianDriver N P F) (s : ℝ≥0) :
    iIndepFun (fun i omega => fun t => coordinate D s i t omega) P := by
  have hm : Measurable (fun f : ℝ≥0 → ℝ => fun t => f (s+t)-f s) :=
    measurable_pi_iff.mpr (fun t => (measurable_pi_apply (s+t)).sub (measurable_pi_apply s))
  exact D.independent.comp (fun _ f => fun t => f (s+t)-f s) (fun _ => hm)

/-- Future vector increments remain independent of the full enlarged
shifted filtration, rather than merely of individual coordinate histories. -/
lemma joint_filtered (D : BrownianDriver N P F) (s u t : ℝ≥0) (hut : u ≤ t) :
    Indep (MeasurableSpace.comap (fun omega i =>
      coordinate D s i t omega-coordinate D s i u omega) inferInstance)
      (filtration F s u) P := by
  have he : (fun omega i => coordinate D s i t omega-coordinate D s i u omega)=
      (fun omega i => D.coordinate i (s+t) omega-D.coordinate i (s+u) omega) := by
    funext omega i
    exact coordinate_increment D s u t i omega
  rw [he]
  exact D.jointFiltered (s+u) (s+t) (add_le_add le_rfl hut)

/-- The genuine shifted driver on the original probability space. -/
@[expose] def driver (D : BrownianDriver N P F) (s : ℝ≥0) :
    BrownianDriver N P (filtration F s) where
  coordinate := coordinate D s
  brownian := coordinate_brownian D s
  filtered := coordinate_filtered D s
  independent := paths_independent D s
  jointFiltered := joint_filtered D s

@[simp] lemma driver_coordinate (D : BrownianDriver N P F) (s : ℝ≥0) (i : Fin N)
    (t : ℝ≥0) (omega : Ω) : (driver D s).coordinate i t omega=
      D.coordinate i (s+t) omega-D.coordinate i s omega := rfl

/-- A state observed at the waiting time is measurable in the genuine
shifted initial sigma algebra. -/
lemma initial_stronglyMeasurable {E : Type*} [TopologicalSpace E]
    (X : ℝ≥0 → Ω → E) (hX : StronglyAdapted F X) (s : ℝ≥0) :
    StronglyMeasurable[filtration F s 0] (X s) := by
  rw [filtration_zero]
  exact hX s

lemma background_stronglyMeasurable {E : Type*} [TopologicalSpace E]
    {Z : Ω → E} (hZ : StronglyMeasurable[F 0] Z) (s : ℝ≥0) :
    StronglyMeasurable[filtration F s 0] Z := by
  rw [filtration_zero]
  exact hZ.mono (F.mono (zero_le : 0 ≤ s))

/-- Null-set information known initially remains known initially after
any deterministic waiting time. -/
lemma null_known_zero (s : ℝ≥0)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∀ A : Set Ω, MeasurableSet A → P A=0 → MeasurableSet[filtration F s 0] A := by
  intro A hm hz
  rw [filtration_zero]
  exact (F.mono (zero_le : 0 ≤ s)) A (hnull A hm hz)

lemma augmented_null_known_zero [IsProbabilityMeasure P] (s : ℝ≥0) :
    ∀ A : Set Ω, MeasurableSet A → P A=0 →
      MeasurableSet[filtration (NullAugmentation.augment F P) s 0] A :=
  null_known_zero s (fun A hm hz => NullAugmentation.augment_null_known_zero F hm hz)

end SphericalAging.ShiftedBrownian
