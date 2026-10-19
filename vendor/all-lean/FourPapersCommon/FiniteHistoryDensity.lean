module
public import FourPapersCommon.FiniteHistory

@[expose] public section

/-! Exact finite path density transport. Each transition is an actual density
relative to a Markov kernel, and the product retains every path coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
variable {State : Type*} [MeasurableSpace State]

def finiteHistoryDensity (w : ℕ → State → State → ℝ≥0∞) :
    (n : ℕ) → FiniteHistory State n → ℝ≥0∞
  | 0 => fun _ => 1
  | n + 1 => fun p =>
      finiteHistoryDensity w n ((historySplit n p).1) *
        w n ((historySplit n p).1 (Fin.last n)) ((historySplit n p).2)

theorem measurable_finiteHistoryDensity (w : ℕ → State → State → ℝ≥0∞)
    (hw : ∀ n, Measurable (Function.uncurry (w n))) (n : ℕ) :
    Measurable (finiteHistoryDensity w n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp ((historySplit n).measurable.fst)).mul
      ((hw n).comp (((measurable_pi_apply _).comp (historySplit n).measurable.fst).prodMk
        (historySplit n).measurable.snd))

@[simp] theorem finiteHistoryDensity_snoc (w : ℕ → State → State → ℝ≥0∞)
    (n : ℕ) (p : FiniteHistory State n) (y : State) :
    finiteHistoryDensity w (n + 1) (Fin.snoc p y) =
      finiteHistoryDensity w n p * w n (p (Fin.last n)) y := by
  change finiteHistoryDensity w n ((historySplit n ((historySplit n).symm (p,y))).1) *
    w n ((historySplit n ((historySplit n).symm (p,y))).1 (Fin.last n))
      ((historySplit n ((historySplit n).symm (p,y))).2) = _
  simp only [MeasurableEquiv.apply_symm_apply]

theorem kernel_comap_withDensity {A : Type*} [MeasurableSpace A]
    (κ κ' : Kernel State State) [IsSFiniteKernel κ] (w : State → State → ℝ≥0∞)
    (hw : Measurable (Function.uncurry w)) (he : κ' = κ.withDensity w)
    (ρ : A → State) (hρ : Measurable ρ) :
    κ'.comap ρ hρ = (κ.comap ρ hρ).withDensity (fun p y => w (ρ p) y) := by
  ext p : 1
  have hp : Measurable (Function.uncurry (fun p y => w (ρ p) y)) :=
    hw.comp (hρ.prodMap measurable_id)
  rw [Kernel.withDensity_apply _ hp]
  change κ' (ρ p) = (κ (ρ p)).withDensity (w (ρ p))
  rw [he, Kernel.withDensity_apply _ hw]

/-- The literal joint density of all states in a finite inhomogeneous Markov
chain is the product of its actual one-step transition densities. -/
theorem finiteHistoryLaw_withDensity (ν : Measure State) [IsProbabilityMeasure ν]
    (κ κ' : ℕ → Kernel State State) (hκ : ∀ n, IsMarkovKernel (κ n))
    (hκ' : ∀ n, IsMarkovKernel (κ' n)) (w : ℕ → State → State → ℝ≥0∞)
    (hw : ∀ n, Measurable (Function.uncurry (w n)))
    (he : ∀ n, κ' n = (κ n).withDensity (w n)) (n : ℕ) :
    finiteHistoryLaw ν κ' n =
      (finiteHistoryLaw ν κ n).withDensity (finiteHistoryDensity w n) := by
  induction n with
  | zero => exact (withDensity_one (μ := finiteHistoryLaw ν κ 0)).symm
  | succ n ih =>
    haveI := hκ n
    haveI := hκ' n
    haveI := isProbabilityMeasure_finiteHistoryLaw ν κ hκ n
    let ρ : FiniteHistory State n → State := fun p => p (Fin.last n)
    have hρ : Measurable ρ := measurable_pi_apply _
    have hmap := kernel_comap_withDensity (κ n) (κ' n) (w n) (hw n) (he n) ρ hρ
    haveI : IsSFiniteKernel (((κ n).comap ρ hρ).withDensity (fun p y => w n (ρ p) y)) := by
      rw [← hmap]
      infer_instance
    change (((finiteHistoryLaw ν κ' n) ⊗ₘ ((κ' n).comap ρ hρ)).map (historySplit n).symm) =
      (((finiteHistoryLaw ν κ n) ⊗ₘ ((κ n).comap ρ hρ)).map (historySplit n).symm).withDensity _
    have hp : Measurable (Function.uncurry (fun p y => w n (ρ p) y)) :=
      (hw n).comp (hρ.prodMap measurable_id)
    rw [ih, hmap, Measure.withDensity_compProd_withDensity
      (measurable_finiteHistoryDensity w hw n) hp]
    have hd := measurable_finiteHistoryDensity w hw (n+1)
    have hm := map_withDensity_pullback
      ((finiteHistoryLaw ν κ n) ⊗ₘ ((κ n).comap ρ hρ))
      (historySplit n).symm (historySplit n).symm.measurable
      (finiteHistoryDensity w (n+1)) hd
    convert! hm using 1
    congr 2
    funext p
    exact (finiteHistoryDensity_snoc w n p.1 p.2).symm

/-- Tilting the actual initial law retains its weight at the first coordinate
of every chronological history. -/
theorem finiteHistoryLaw_withDensity_initial (ν ν' : Measure State)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (κ : ℕ → Kernel State State) (hκ : ∀ n, IsMarkovKernel (κ n))
    (w₀ : State→ℝ≥0∞) (hw₀ : Measurable w₀) (hν : ν'=ν.withDensity w₀) (n:ℕ) :
    finiteHistoryLaw ν' κ n=(finiteHistoryLaw ν κ n).withDensity
      (fun p=>w₀ (p 0)) := by
  induction n with
  | zero =>
    change ν'.map (fun x _=>x)=(ν.map (fun x _=>x)).withDensity (fun p:FiniteHistory State 0=>w₀ (p 0))
    rw [hν]
    exact map_withDensity_pullback ν (fun x _=>x) (by fun_prop)
      (fun p:FiniteHistory State 0=>w₀ (p 0)) (hw₀.comp (measurable_pi_apply 0))
  | succ n ih =>
    haveI:=hκ n
    haveI:=isProbabilityMeasure_finiteHistoryLaw ν κ hκ n
    change ((finiteHistoryLaw ν' κ n) ⊗ₘ
      ((κ n).comap (fun p=>p (Fin.last n)) (measurable_pi_apply _))).map (historySplit n).symm=
      (((finiteHistoryLaw ν κ n) ⊗ₘ
      ((κ n).comap (fun p=>p (Fin.last n)) (measurable_pi_apply _))).map (historySplit n).symm).withDensity _
    have hd₀ : Measurable (fun p:FiniteHistory State n=>w₀ (p 0)) :=
      hw₀.comp (measurable_pi_apply 0)
    rw [ih,Measure.withDensity_compProd (f:=fun p:FiniteHistory State n=>w₀ (p 0)) hd₀]
    have hm:=map_withDensity_pullback
      ((finiteHistoryLaw ν κ n) ⊗ₘ
        ((κ n).comap (fun p=>p (Fin.last n)) (measurable_pi_apply _)))
      (historySplit n).symm (historySplit n).symm.measurable
      (fun p:FiniteHistory State (n+1)=>w₀ (p 0)) (hw₀.comp (measurable_pi_apply 0))
    convert hm using 1
    congr 2

/-- The full path density includes both the initial tilt and all actual
transition tilts. -/
theorem finiteHistoryLaw_withDensity_initial_and_transitions (ν ν' : Measure State)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (κ κ' : ℕ→Kernel State State) (hκ:∀n,IsMarkovKernel (κ n))
    (hκ':∀n,IsMarkovKernel (κ' n))
    (w₀:State→ℝ≥0∞) (hw₀:Measurable w₀) (hν:ν'=ν.withDensity w₀)
    (w:ℕ→State→State→ℝ≥0∞) (hw:∀n,Measurable (Function.uncurry (w n)))
    (he:∀n,κ' n=(κ n).withDensity (w n)) (n:ℕ) :
    finiteHistoryLaw ν' κ' n=(finiteHistoryLaw ν κ n).withDensity
      (fun p=>w₀ (p 0)*finiteHistoryDensity w n p) := by
  rw [finiteHistoryLaw_withDensity ν' κ κ' hκ hκ' w hw he,
    finiteHistoryLaw_withDensity_initial ν ν' κ hκ w₀ hw₀ hν]
  have hd₀ : Measurable (fun p:FiniteHistory State n=>w₀ (p 0)) :=
    hw₀.comp (measurable_pi_apply 0)
  exact (withDensity_mul _ hd₀ (measurable_finiteHistoryDensity w hw n)).symm

end FourPapersCommon
