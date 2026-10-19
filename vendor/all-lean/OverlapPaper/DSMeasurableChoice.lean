module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Bases

@[expose] public section

/-! A measurable approximate-choice lemma for spectral rotations. It chooses
the first suitable point of a fixed countable dense sequence; it does not
postulate a measurable selection of an arbitrary eigenbasis. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 800000

theorem exists_measurable_approximate_choice {X K : Type*}
    [MeasurableSpace X] [TopologicalSpace K] [SeparableSpace K] [Nonempty K]
    [MeasurableSpace K] (cost : X → K → ℝ) (b : X → ℝ)
    (hc : ∀ k,Measurable (fun x => cost x k)) (hb : Measurable b)
    (hcont : ∀ x,Continuous (cost x)) (ε : ℝ) (hε : 0 < ε)
    (hfeasible : ∀ x,∃ k,cost x k ≤ b x) :
    ∃ g : X → K,Measurable g ∧ ∀ x,cost x (g x) < b x+ε := by
  let d := denseSeq K
  have hp : ∀ x,∃ n : ℕ,cost x (d n) < b x+ε := by
    intro x
    obtain ⟨k,hk⟩ := hfeasible x
    have ho : IsOpen {z : K | cost x z < b x+ε} :=
      isOpen_Iio.preimage (hcont x)
    have hne : ({z : K | cost x z < b x+ε} : Set K).Nonempty := ⟨k,by change cost x k < b x+ε; linarith⟩
    obtain ⟨n,hn⟩ := (denseRange_denseSeq K).exists_mem_open ho hne
    exact ⟨n,hn⟩
  let index : X → ℕ := fun x => Nat.find (hp x)
  have hm : Measurable index := measurable_find hp
    (fun n => measurableSet_lt (hc (d n)) (hb.add measurable_const))
  refine ⟨fun x => d (index x),(measurable_of_countable d).comp hm,?_⟩
  intro x
  exact Nat.find_spec (hp x)

end OverlapPaper
