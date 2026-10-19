module

public import SphericalAging.VectorBrownian
public import SphericalAging.VectorIto

public section

/-! Reveal arbitrary independent background randomness at time zero while
preserving the actual joint vector-increment independence. The enlarged
filtration is exactly the product of the background sigma algebra with F_t,
matching the joint adapted parameter-solution construction.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.IndependentBackgroundDriver
open HardSphereDynamics
variable {A Ω : Type*} [mA : MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℕ}

/-- True product filtration: all independent background is known at zero. -/
@[expose] def filtration (A : Type*) [MeasurableSpace A] {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (A × Ω)) where
  seq t := (inferInstance : MeasurableSpace A).prod (F t)
  mono' := fun _ _ hst => sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.mono hst))
  le' t := sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le t))

lemma background_known (t : ℝ≥0) :
    Measurable[filtration A F t] (Prod.fst : A × Ω → A) := measurable_fst

lemma base_known (t : ℝ≥0) :
    @Measurable (A × Ω) Ω (filtration A F t) (F t) Prod.snd := measurable_snd

/-- Future joint increments stay independent of the background together
with the complete old past. -/
lemma joint_increment_independent (D : BrownianDriver N P F) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun q : A × Ω => fun i => D.coordinate i t q.2-D.coordinate i s q.2)
      inferInstance) (filtration A F s) (ρ.prod P) := by
  let f := fun ω : Ω => fun i => D.coordinate i t ω-D.coordinate i s ω
  have hf : Measurable f := measurable_pi_iff.mpr (fun i =>
    (D.coordinateStronglyMeasurable i t).measurable.sub (D.coordinateStronglyMeasurable i s).measurable)
  let : MeasurableSpace (ULift.{0} Ω) := MeasurableSpace.comap ULift.down (F s)
  have hg : Measurable (ULift.up : Ω → ULift.{0} Ω) := by
    rw [measurable_iff_comap_le,MeasurableSpace.comap_comp]
    change MeasurableSpace.comap id (F s) ≤ mΩ
    rw [MeasurableSpace.comap_id]
    exact F.le s
  have hi : IndepFun f (ULift.up : Ω → ULift.{0} Ω) P := by
    rw [IndepFun_iff_Indep]
    change Indep _ (MeasurableSpace.comap ULift.up (MeasurableSpace.comap ULift.down (F s))) P
    rw [MeasurableSpace.comap_comp]
    change Indep _ (MeasurableSpace.comap id (F s)) P
    rw [MeasurableSpace.comap_id]
    exact D.jointFiltered s t hst
  have h := VectorBrownian.independent_background_and_past ρ P f (ULift.up : Ω → ULift.{0} Ω) hf hg hi
  have hh := (IndepFun_iff_Indep _ _ _).1 h
  change Indep _ (MeasurableSpace.comap (fun q : A × Ω => (q.1,ULift.up q.2))
    (mA.prod (MeasurableSpace.comap ULift.down (F s)))) (ρ.prod P) at hh
  rw [MeasurableSpace.comap_prodMk,MeasurableSpace.comap_comp] at hh
  exact hh

lemma coordinate_brownian (D : BrownianDriver N P F) (i : Fin N) :
    IsBrownianMotion (fun t (q : A × Ω) => D.coordinate i t q.2) (ρ.prod P) where
  toIsPreBrownianReal := {
    hasLaw := fun I => ((D.brownian i).hasLaw I).comp measurePreserving_snd.hasLaw }
  cont := measurePreserving_snd.quasiMeasurePreserving.ae (D.brownian i).cont

omit [IsProbabilityMeasure P] in
lemma coordinate_adapted (D : BrownianDriver N P F) (i : Fin N) :
    StronglyAdapted (filtration A F) (fun t (q : A × Ω) => D.coordinate i t q.2) := by
  intro t
  exact ((D.filtered i).stronglyAdapted t).comp_measurable (base_known (A := A) t)

lemma coordinate_filtered (D : BrownianDriver N P F) (i : Fin N) :
    IsFilteredPreBrownian (fun t (q : A × Ω) => D.coordinate i t q.2) (filtration A F) (ρ.prod P) where
  toIsPreBrownianReal := (coordinate_brownian D i).toIsPreBrownianReal
  stronglyAdapted := coordinate_adapted D i
  indep s t hst := by
    have hj := joint_increment_independent (ρ := ρ) D hst
    have hcomp : MeasurableSpace.comap (fun q : A × Ω => D.coordinate i t q.2-D.coordinate i s q.2)
        inferInstance ≤ MeasurableSpace.comap (fun q : A × Ω => fun j => D.coordinate j t q.2-D.coordinate j s q.2)
          inferInstance := by
      have he : MeasurableSpace.comap (fun q : A × Ω => D.coordinate i t q.2-D.coordinate i s q.2) inferInstance =
          MeasurableSpace.comap (fun q : A × Ω => fun j : Fin N => D.coordinate j t q.2-D.coordinate j s q.2)
            (MeasurableSpace.comap (fun v : Fin N → ℝ => v i) inferInstance) := by
        rw [MeasurableSpace.comap_comp]
        rfl
      rw [he]
      change MeasurableSpace.comap (fun q : A × Ω => fun j : Fin N => D.coordinate j t q.2-D.coordinate j s q.2)
        (MeasurableSpace.comap (fun v : Fin N → ℝ => v i) inferInstance) ≤ _
      exact MeasurableSpace.comap_mono (measurable_pi_apply i).comap_le
    exact indep_of_indep_of_le_left hj hcomp

lemma paths_independent (D : BrownianDriver N P F) :
    iIndepFun (fun i (q : A × Ω) => fun t => D.coordinate i t q.2) (ρ.prod P) := by
  have hm : ∀ i : Fin N, Measurable (fun ω : Ω => fun t => D.coordinate i t ω) :=
    fun i => measurable_pi_iff.mpr (fun t => (D.coordinateStronglyMeasurable i t).measurable)
  change iIndepFun (fun i => (fun ω : Ω => fun t => D.coordinate i t ω) ∘ (Prod.snd : A × Ω → Ω)) (ρ.prod P)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).comp measurable_snd |>.aemeasurable)]
  have hs : (ρ.prod P).map (Prod.snd : A × Ω → Ω)=P := measurePreserving_snd.map_eq
  have hmaps : ∀ i : Fin N, (ρ.prod P).map (fun q : A × Ω => fun t => D.coordinate i t q.2)=
      P.map (fun ω : Ω => fun t => D.coordinate i t ω) := by
    intro i
    change (ρ.prod P).map ((fun ω : Ω => fun t => D.coordinate i t ω) ∘ Prod.snd)=_
    rw [← Measure.map_map (hm i) measurable_snd,hs]
  have hmvec : Measurable (fun ω : Ω => fun i t => D.coordinate i t ω) := measurable_pi_iff.mpr hm
  change (ρ.prod P).map ((fun ω : Ω => fun i t => D.coordinate i t ω) ∘ Prod.snd)=_
  rw [← Measure.map_map hmvec measurable_snd,hs]
  change P.map (fun ω : Ω => fun i t => D.coordinate i t ω)=
    Measure.pi (fun i : Fin N => (ρ.prod P).map (fun q : A × Ω => fun t => D.coordinate i t q.2))
  simp_rw [hmaps]
  exact D.independent.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)

/-- Actual driver on independent background × original Brownian space. -/
@[expose] def driver (D : BrownianDriver N P F) : BrownianDriver N (ρ.prod P) (filtration A F) where
  coordinate i t q := D.coordinate i t q.2
  brownian := coordinate_brownian D
  filtered := coordinate_filtered D
  independent := paths_independent D
  jointFiltered := fun _ _ hst => joint_increment_independent D hst

end SphericalAging.IndependentBackgroundDriver
