module
public import FourPapersCommon.FiniteHistory
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! An explicit independent-coordinate construction of a finite Markov path.
No conditional transition law is supplied: every transition is the actual
pushforward of one independent coordinate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FourPapersCommon

variable {State Noise : Type*} [MeasurableSpace State] [MeasurableSpace Noise]

def noiseSplit (m : ℕ) : (Fin (m+1) → Noise) ≃ᵐ (Fin m → Noise) × Noise :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Noise) (Fin.last m)).trans
    MeasurableEquiv.prodComm

@[simp] theorem noiseSplit_apply (m : ℕ) (z : Fin (m+1) → Noise) :
    noiseSplit m z = (fun i => z i.castSucc,z (Fin.last m)) := by
  simp [noiseSplit,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm]
  rfl

theorem noiseSplit_map (η : Measure Noise) [IsProbabilityMeasure η] (m : ℕ) :
    (Measure.pi (fun _ : Fin (m+1) => η)).map (noiseSplit m) =
      (Measure.pi (fun _ : Fin m => η)).prod η := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => η) (Fin.last m)
  rw [noiseSplit,MeasurableEquiv.coe_trans,←Measure.map_map
    MeasurableEquiv.prodComm.measurable h.measurable,h.map_eq]
  exact Measure.prod_swap

def independentHistory (update : ℕ → State → Noise → State) :
    (m : ℕ) → State × (Fin m → Noise) → FiniteHistory State m
  | 0, p => fun _ => p.1
  | m+1, p =>
      let h := independentHistory update m (p.1,fun i => p.2 i.castSucc)
      Fin.snoc h (update m (h (Fin.last m)) (p.2 (Fin.last m)))

theorem measurable_independentHistory (update : ℕ → State → Noise → State)
    (hu : ∀ i,Measurable (Function.uncurry (update i))) (m : ℕ) :
    Measurable (independentHistory update m) := by
  induction m with
  | zero => exact Measurable.of_eval fun _ => measurable_fst
  | succ m ih =>
    have hp : Measurable (fun p : State × (Fin (m+1) → Noise) =>
        (p.1,fun i : Fin m => p.2 i.castSucc)) :=
      measurable_fst.prodMk (Measurable.of_eval fun i =>
        (measurable_pi_apply i.castSucc).comp measurable_snd)
    have hh := ih.comp hp
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [independentHistory,Fin.snoc_last,Function.comp_def,Function.uncurry_apply_pair] using
        (hu m).comp (((measurable_pi_apply (Fin.last m)).comp hh).prodMk
          ((measurable_pi_apply (Fin.last m)).comp measurable_snd))
    · simpa only [independentHistory,Fin.snoc_castSucc,Function.comp_def] using
        (measurable_pi_apply j).comp hh

theorem independent_update_joint_law {A B C E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace E]
    (P : Measure A) (Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : A → B) (hf : Measurable f) (u : B → E → C)
    (hu : Measurable (Function.uncurry u)) (κ : Kernel B C) [IsMarkovKernel κ]
    (hk : ∀ b,κ b=Q.map (u b)) :
    (P.prod Q).map (fun p => (f p.1,u (f p.1) p.2)) = P.map f ⊗ₘ κ := by
  have hj : Measurable (fun p : A × E => (f p.1,u (f p.1) p.2)) :=
    (hf.comp measurable_fst).prodMk (hu.comp ((hf.comp measurable_fst).prodMk measurable_snd))
  ext S hS
  rw [Measure.map_apply hj hS,Measure.prod_apply (hS.preimage hj),
    Measure.compProd_apply hS,lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hf]
  apply lintegral_congr
  intro x
  have hux : Measurable (u (f x)) := by
    simpa only [Function.comp_def,Function.uncurry_apply_pair,id_eq] using
      hu.comp (measurable_const.prodMk measurable_id)
  rw [hk,Measure.map_apply hux (measurable_prodMk_left hS)]
  rfl

def independentCoordinateSplit (m : ℕ) :
    State × (Fin (m+1) → Noise) ≃ᵐ (State × (Fin m → Noise)) × Noise :=
  ((MeasurableEquiv.refl State).prodCongr (noiseSplit m)).trans MeasurableEquiv.prodAssoc.symm

@[simp] theorem independentCoordinateSplit_apply (m : ℕ)
    (p : State × (Fin (m+1) → Noise)) :
    independentCoordinateSplit m p = ((p.1,fun i => p.2 i.castSucc),p.2 (Fin.last m)) := by
  simp [independentCoordinateSplit,MeasurableEquiv.prodCongr,MeasurableEquiv.prodAssoc]

theorem independentCoordinateSplit_map (ν : Measure State) (η : Measure Noise)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (m : ℕ) :
    (ν.prod (Measure.pi (fun _ : Fin (m+1) => η))).map (independentCoordinateSplit m) =
      (ν.prod (Measure.pi (fun _ : Fin m => η))).prod η := by
  have hn : MeasurePreserving (noiseSplit m) (Measure.pi (fun _ : Fin (m+1) => η))
      ((Measure.pi (fun _ : Fin m => η)).prod η) :=
    ⟨(noiseSplit m).measurable,noiseSplit_map η m⟩
  have hp := (MeasurePreserving.id ν).prod hn
  have ha := (measurePreserving_prodAssoc ν (Measure.pi (fun _ : Fin m => η)) η).symm
  exact (ha.comp hp).map_eq

theorem independentHistory_law (ν : Measure State) (η : Measure Noise)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (update : ℕ → State → Noise → State)
    (hu : ∀ i,Measurable (Function.uncurry (update i)))
    (κ : ℕ → Kernel State State) (hκ : ∀ i,IsMarkovKernel (κ i))
    (hk : ∀ i x,κ i x=η.map (update i x)) (m : ℕ) :
    (ν.prod (Measure.pi (fun _ : Fin m => η))).map (independentHistory update m) =
      finiteHistoryLaw ν κ m := by
  induction m with
  | zero =>
    rw [Measure.pi_of_empty,Measure.prod_dirac,Measure.map_map
      (measurable_independentHistory update hu 0) measurable_prodMk_right]
    rfl
  | succ m ih =>
    haveI := hκ m
    let f := independentHistory update m
    have hf : Measurable f := measurable_independentHistory update hu m
    let u : FiniteHistory State m → Noise → State :=
      fun h z => update m (h (Fin.last m)) z
    have hu' : Measurable (Function.uncurry u) := by
      have hp : Measurable (fun p : FiniteHistory State m × Noise =>
          (p.1 (Fin.last m),p.2)) :=
        ((measurable_pi_apply (Fin.last m)).comp measurable_fst).prodMk measurable_snd
      convert (hu m).comp hp using 1
      funext p
      cases p
      rfl
    have hj := independent_update_joint_law
      (ν.prod (Measure.pi (fun _ : Fin m => η))) η f hf u hu'
      ((κ m).comap (fun h => h (Fin.last m)) (measurable_pi_apply _))
      (fun h => by rw [Kernel.comap_apply];exact hk m _)
    have hfunc : independentHistory update (m+1) =
        ((historySplit m).symm ∘ (fun p => (f p.1,u (f p.1) p.2))) ∘
          independentCoordinateSplit m := by
      funext p
      simp [independentCoordinateSplit_apply,independentHistory,Function.comp_def,f,u]
    have hjm : Measurable (fun p : (State × (Fin m → Noise)) × Noise =>
        (f p.1,u (f p.1) p.2)) := by
      simpa only [Function.comp_def,Function.uncurry] using
        (hf.comp measurable_fst).prodMk (hu'.comp ((hf.comp measurable_fst).prodMk measurable_snd))
    rw [hfunc,←Measure.map_map
      ((historySplit m).symm.measurable.comp hjm)
      (independentCoordinateSplit m).measurable,independentCoordinateSplit_map,
      ←Measure.map_map (historySplit m).symm.measurable hjm,
      hj]
    change (( (ν.prod (Measure.pi (fun _ : Fin m => η))).map (independentHistory update m)) ⊗ₘ _).map _ = _
    rw [ih]
    rfl

end FourPapersCommon
