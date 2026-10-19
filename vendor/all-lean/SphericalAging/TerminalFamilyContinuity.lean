module

public import SphericalAging.TerminalTimeContinuity
public import SphericalAging.TerminalStateRepresentation

public section
/-! Joint continuity of actual terminal classes from continuous source rows. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.TerminalFamilyContinuity
open HardSphereDynamics LocalSDE TerminalLinearity TerminalStateRepresentation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem terminalClass_joint_continuous (D : BrownianDriver N P F) (T : ℝ≥0)
    (A : State N → State N) (R : State N → Fin N → PredictableProcessL2 F P)
    (S : State N → Fin N → Fin N → PredictableProcessL2 F P)
    (hA : Continuous A) (hR : ∀ i,Continuous (fun x => R x i))
    (hS : ∀ i j,Continuous (fun x => S x i j)) :
    Continuous (fun z : ℝ≥0 × State N => terminalClass D (A z.2) (R z.2) (S z.2) T z.1) := by
  classical
  have hd (i : Fin N) : Continuous (fun z : ℝ≥0 × State N => driftTerminalOperator T z.1 (R z.2 i)) := by
    have hh := (TerminalTimeContinuity.driftTerminal_joint_continuous (F := F) (P := P) T).comp
      (continuous_fst.prodMk ((hR i).comp continuous_snd))
    exact hh.congr (fun z => rfl)
  have hn (i j : Fin N) : Continuous (fun z : ℝ≥0 × State N => itoTerminalOperator D j z.1 (S z.2 i j)) := by
    have hh := (TerminalTimeContinuity.itoTerminal_joint_continuous D j).comp
      (continuous_fst.prodMk ((hS i j).comp continuous_snd))
    exact hh.congr (fun z => rfl)
  have hsum : Continuous (fun z : ℝ≥0 × State N => ∑ i : Fin N,stateTerminalInclusion i
      (driftTerminalOperator T z.1 (R z.2 i)+∑ j : Fin N,itoTerminalOperator D j z.1 (S z.2 i j))) := by
    apply continuous_finset_sum
    intro i _
    apply (stateTerminalInclusion i).continuous.comp
    exact (hd i).add (continuous_finset_sum _ (fun j _ => hn i j))
  exact ((initialTerminalOperator (N := N) (P := P)).continuous.comp (hA.comp continuous_snd)).add hsum
end SphericalAging.TerminalFamilyContinuity
