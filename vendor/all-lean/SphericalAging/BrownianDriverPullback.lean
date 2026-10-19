module

public import SphericalAging.NullAugmentation
public import Mathlib.Probability.Independence.Basic

public section

/-! A genuine measure-preserving path sampler pulls the entire Brownian
driver back to the literal inverse-image filtration. This retains full
coordinate path independence and joint increment independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal
namespace SphericalAging.BrownianDriverPullback
open HardSphereDynamics
set_option maxHeartbeats 1200000
variable {Ω Ω' : Type*} [m : MeasurableSpace Ω] [m' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 m} {N : ℕ} {φ : Ω'→Ω}

@[expose] def filtration (F : Filtration ℝ≥0 m) (hφ : Measurable φ) : Filtration ℝ≥0 m' where
  seq t := (F t).comap φ
  mono' := fun _ _ h => MeasurableSpace.comap_mono (F.mono h)
  le' t := (MeasurableSpace.comap_mono (F.le t)).trans hφ.comap_le

theorem filtered (F : Filtration ℝ≥0 m) (hφ : Measurable φ) (t : ℝ≥0) :
    @Measurable Ω' Ω (filtration F hφ t) (F t) φ := comap_measurable φ

theorem augmented_filtered (hφ : MeasurePreserving φ Q P) (t : ℝ≥0) :
    @Measurable Ω' Ω (NullAugmentation.augment (filtration F hφ.measurable) Q t)
      (NullAugmentation.augment F P t) φ := by
  intro A hA
  obtain ⟨B,hB,hAB⟩ := hA.2
  refine ⟨hφ.measurable hA.1,φ⁻¹'B,(filtered F hφ.measurable t) hB,?_⟩
  exact hφ.quasiMeasurePreserving.ae hAB

theorem indep_pullback (hφ : MeasurePreserving φ Q P) {m1 m2 : MeasurableSpace Ω}
    (h1 : m1≤m) (h2 : m2≤m) (hi : Indep m1 m2 P) :
    Indep (m1.comap φ) (m2.comap φ) Q := by
  apply (indep_iff_forall_indepSet Q).mpr
  rintro A B ⟨C,hC,rfl⟩ ⟨D,hD,rfl⟩
  letI : MeasurableSpace Ω := m
  have hCm : MeasurableSet C := h1 _ hC
  have hDm : MeasurableSet D := h2 _ hD
  apply (indepSet_iff_measure_inter_eq_mul (hφ.measurable hCm)
    (hφ.measurable hDm) Q).mpr
  rw [←preimage_inter,hφ.measure_preimage (hCm.inter hDm).nullMeasurableSet,
    hφ.measure_preimage hCm.nullMeasurableSet,hφ.measure_preimage hDm.nullMeasurableSet]
  exact ((indepSet_iff_measure_inter_eq_mul hCm hDm P).mp
    (hi.indepSet_of_measurableSet hC hD))

theorem coordinate_brownian (D : BrownianDriver N P F) (hφ : MeasurePreserving φ Q P)
    (i : Fin N) : IsBrownianMotion (fun t omega => D.coordinate i t (φ omega)) Q where
  toIsPreBrownianReal := {
    hasLaw := fun I => ((D.brownian i).hasLaw I).comp hφ.hasLaw }
  cont := hφ.quasiMeasurePreserving.ae (D.brownian i).cont

theorem coordinate_filtered (D : BrownianDriver N P F) (hφ : MeasurePreserving φ Q P)
    (i : Fin N) : IsFilteredPreBrownian (fun t omega => D.coordinate i t (φ omega))
      (filtration F hφ.measurable) Q where
  toIsPreBrownianReal := (coordinate_brownian D hφ i).toIsPreBrownianReal
  stronglyAdapted := fun t => ((D.filtered i).stronglyAdapted t).comp_measurable
    (comap_measurable φ)
  indep s t hst := by
    change Indep (MeasurableSpace.comap
      (fun omega => D.coordinate i t (φ omega)-D.coordinate i s (φ omega)) inferInstance)
      ((F s).comap φ) Q
    have hi := indep_pullback hφ
      (((D.coordinateStronglyMeasurable i t).measurable.sub
        (D.coordinateStronglyMeasurable i s).measurable).comap_le)
      (F.le s) ((D.filtered i).indep s t hst)
    simpa only [filtration,MeasurableSpace.comap_comp,Function.comp_def,Pi.sub_apply] using hi

theorem paths_independent (D : BrownianDriver N P F) (hφ : MeasurePreserving φ Q P) :
    iIndepFun (fun i omega => fun t => D.coordinate i t (φ omega)) Q := by
  have hm : ∀i : Fin N,Measurable (fun omega : Ω => fun t => D.coordinate i t omega) :=
    fun i => measurable_pi_iff.mpr (fun t => (D.coordinateStronglyMeasurable i t).measurable)
  change iIndepFun (fun i => (fun omega : Ω => fun t => D.coordinate i t omega) ∘ φ) Q
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hm i).comp hφ.measurable).aemeasurable)]
  have hmvec : Measurable (fun omega : Ω => fun i t => D.coordinate i t omega) :=
    measurable_pi_iff.mpr hm
  change Q.map ((fun omega : Ω => fun i t => D.coordinate i t omega) ∘ φ)=_
  rw [←Measure.map_map hmvec hφ.measurable,hφ.map_eq]
  have hmarg : ∀i : Fin N,Q.map (fun omega : Ω' => fun t => D.coordinate i t (φ omega))=
      P.map (fun omega : Ω => fun t => D.coordinate i t omega) := by
    intro i
    change Q.map ((fun omega : Ω => fun t => D.coordinate i t omega) ∘ φ)=_
    rw [←Measure.map_map (hm i) hφ.measurable,hφ.map_eq]
  simpa only [Function.comp_def,hmarg] using
    (D.independent.map_fun_eq_pi_map (fun i => (hm i).aemeasurable))

/-- The actual pulled-back driver has no probabilistic conclusion as a
premise: all laws and independence follow from the sampler's true law. -/
@[expose] def driver (D : BrownianDriver N P F) (hφ : MeasurePreserving φ Q P) :
    BrownianDriver N Q (filtration F hφ.measurable) where
  coordinate i t omega := D.coordinate i t (φ omega)
  brownian := coordinate_brownian D hφ
  filtered := coordinate_filtered D hφ
  independent := paths_independent D hφ
  jointFiltered s t hst := by
    have hi := indep_pullback hφ
      ((measurable_pi_iff.mpr (fun i => (D.coordinateStronglyMeasurable i t).measurable.sub
        (D.coordinateStronglyMeasurable i s).measurable)).comap_le)
      (F.le s) (D.jointFiltered s t hst)
    simpa only [filtration,MeasurableSpace.comap_comp,Function.comp_def,Pi.sub_apply] using hi

end SphericalAging.BrownianDriverPullback
