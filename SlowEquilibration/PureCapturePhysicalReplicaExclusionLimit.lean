-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticFullLift

/-! Transfer of actual finite-dimensional Gibbs replica exclusion to
every genuine n→∞ physical overlap-array weak limit. The events are
open, so Portmanteau gives the required direction of inequality. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticScoreLimits
open PureCapturePhysicalAsymptoticFullLift
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- An open event whose genuine annealed Gibbs probability decays along
all physical dimensions has zero mass at every asymptotic overlap limit. -/
theorem asymptoticFullOverlapLaw_open_zero_of_physical_decay
    (μ : FiniteMixture) (β : ℝ) (m : ℕ)
    (E : Set (FullOverlapCoordinates m)) (hE : IsOpen E)
    (hdecay : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := m) μ β :
        Measure (FullOverlapCoordinates m)) E) atTop (𝓝 0))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    (x m : Measure (FullOverlapCoordinates m)) E = 0 := by
  obtain ⟨s, hs, hfull⟩ :=
    ((mem_tailClusterSet_iff_mapClusterPt _ _).1 hx).tendsto_subseq
  have hm : Tendsto
      (fun j => physicalFullOverlapLaw (n := s j) (m := m) μ β)
      atTop (𝓝 (x m)) := by
    exact ((continuous_apply m).tendsto x).comp hfull
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hm hE
  have hdecay' := hdecay.comp hs.tendsto_atTop
  have hliminf : liminf (fun j =>
      (physicalFullOverlapLaw (n := s j) (m := m) μ β :
        Measure (FullOverlapCoordinates m)) E) atTop = 0 := by
    simpa only [Function.comp_def] using hdecay'.liminf_eq
  rw [hliminf] at hport
  exact le_zero_iff.mp hport

def fullEquilateralEvent (m : ℕ) (q ρ : ℝ) :
    Set (FullOverlapCoordinates m) :=
  {c | ∀ i j : Fin m, i ≠ j → |c i j - q| < ρ}

theorem fullEquilateralEvent_open (m : ℕ) (q ρ : ℝ) :
    IsOpen (fullEquilateralEvent m q ρ) := by
  unfold fullEquilateralEvent
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using
      (isOpen_lt (((continuous_apply j).comp (continuous_apply i)).sub
        continuous_const).abs continuous_const)

theorem asymptoticFullOverlapLaw_equilateral_zero_of_physical_decay
    (μ : FiniteMixture) (β : ℝ) (m : ℕ) (q ρ : ℝ)
    (hdecay : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := m) μ β :
        Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
      atTop (𝓝 0))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    (x m : Measure (FullOverlapCoordinates m))
      (fullEquilateralEvent m q ρ) = 0 :=
  asymptoticFullOverlapLaw_open_zero_of_physical_decay
    μ β m _ (fullEquilateralEvent_open m q ρ) hdecay hx

def fullPairCapEvent (a : ℝ) : Set (FullOverlapCoordinates 2) :=
  {c | a < c 0 1}

theorem fullPairCapEvent_open (a : ℝ) : IsOpen (fullPairCapEvent a) := by
  exact isOpen_lt continuous_const
    ((continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2)))

theorem asymptoticFullOverlapLaw_pairCap_zero_of_physical_decay
    (μ : FiniteMixture) (β a : ℝ)
    (hdecay : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)) (fullPairCapEvent a))
      atTop (𝓝 0))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    (x 2 : Measure (FullOverlapCoordinates 2))
      (fullPairCapEvent a) = 0 :=
  asymptoticFullOverlapLaw_open_zero_of_physical_decay
    μ β 2 _ (fullPairCapEvent_open a) hdecay hx

end SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
