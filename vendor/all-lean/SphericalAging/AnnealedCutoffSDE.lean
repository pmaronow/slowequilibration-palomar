module

public import SphericalAging.AnnealedCutoffCoefficients
public import SphericalAging.AnnealedSDECore

public section

/-! The actual annealed cutoff Hamiltonian process satisfies its true
random-disorder matrix SDE on the enlarged independent-background
filtration. All evaluated predictable coefficient classes and actual
Itô terminal operators have been identified in prior proved lemmas.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedCutoffSDE
open HardSphereDynamics AnnealedCutoffProcess AnnealedCutoffCoefficients AnnealedSDECore
open IndependentBackgroundDriver
set_option maxHeartbeats 1000000
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {ρ : Measure (Parameter N p)} [IsProbabilityMeasure ρ]

lemma process_apply (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T t : ℝ≥0)
    (ω : Parameter N p × Ω) (i : Fin N) :
    (process D β R hR hJ T t ω) i = AnnealedCutoffProcess.coordinateProcess D β R hR hJ T i t ω := by
  simp [process,basisVector,Pi.single_apply]

/-- Genuine strong existence on every horizon with random independent
disorder and random independent initial state known at time zero. -/
theorem process_strongSolution (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) :
    IsRandomStrongSolutionOn (driver (ρ := ρ) D)
      (fun ω i x => CutoffSDE.cutoffDrift β ω.1.1 R hR i x)
      (fun _ i j x => CutoffSDE.cutoffNoise N R hR i j x)
      (fun ω => ω.1.2) (process D β R hR hJ T) T := by
  refine ⟨(continuous_snd : Continuous (Prod.snd : Parameter N p → State N)).stronglyMeasurable.comp_measurable
    (background_known 0),process_stronglyAdapted D β R hR hJ T,process_continuous D β R hR hJ T,
    driftLift D β R hR hJ T,(fun i j => noiseLift (ρ := ρ) (p := p) D β R hR T i j),
    (fun i => driftLift_coe D β R hR hJ T i),(fun i j => noiseLift_coe D β R hR hJ T i j),?_⟩
  intro t ht i
  have hd := driftVersion_eq_actual (driftLift D β R hR hJ T i)
    (driftProcess D β R hR hJ T i) T (driftLift_coe D β R hR hJ T i)
  have hn := vectorProcessLp_ae_itoVersions (driver (ρ := ρ) D)
    (fun j => noiseLift (ρ := ρ) (p := p) D β R hR T i j) t
  filter_upwards [hd,hn] with ω hd hn
  rw [process_apply]
  change AnnealedCutoffProcess.coordinateProcess D β R hR hJ T i t ω = _
  unfold AnnealedCutoffProcess.coordinateProcess
  rw [hd t ht,hn]
  rfl

end SphericalAging.AnnealedCutoffSDE
