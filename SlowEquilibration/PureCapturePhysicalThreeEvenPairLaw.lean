-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairPowerWeakLimit
public import SlowEquilibration.PureCaptureThreeEvenMomentLaw

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalThreeEvenPairLaw

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticFullLift PureCapturePhysicalFullArrayCubeSupport
open PureCapturePhysicalPairPowerWeakLimit
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Equality in the three-moment Jensen bound identifies both the support
and the nonzero mass of the actual pair law. No support hypothesis is used. -/
theorem pair_law_support_and_mass_of_three_even_moments
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ z ∂ν, z ∈ fullOverlapCube 2)
    (x Q : ℝ) (hQ : 0 < Q)
    (a b c : ℕ) (ha0 : 0 < a) (hab : a < b) (hbc : b < c)
    (ha : Even a) (hb : Even b) (hc : Even c)
    (hA : (∫ z, (z 0 1) ^ a ∂ν) = (1 - x) * Q ^ a)
    (hB : (∫ z, (z 0 1) ^ b ∂ν) = (1 - x) * Q ^ b)
    (hC : (∫ z, (z 0 1) ^ c ∂ν) = (1 - x) * Q ^ c) :
    (∀ᵐ z ∂ν, z 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) ∧
      ν.real {z | |z 0 1| = Q} = 1 - x := by
  have hpower (p : ℕ) : Integrable (fun z : FullOverlapCoordinates 2 =>
      (z 0 1) ^ p) ν := by
    have hcont : Continuous (fun z : FullOverlapCoordinates 2 => (z 0 1) ^ p) := by
      fun_prop
    have hi := hcont.continuousOn.integrableOn_compact (fullOverlapCube_compact 2) (μ := ν)
    simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hcube] using hi
  exact PureCaptureThreeEvenMomentLaw.support_and_mass_of_three_even_moments ν
    (fun z => z 0 1) (by fun_prop) x Q hQ a b c ha0 hab hbc ha hb hc
    (hpower a) (hpower b) (hpower c) hA hB hC

/-- Source `prop:dir-even`'s pair-law support and exact mass conclusions for
every genuine physical full-array weak limit, derived from the three physical
moment limits. -/
theorem asymptotic_pair_law_support_and_mass
    (μ : FiniteMixture) (β x Q : ℝ) (hQ : 0 < Q)
    (a b c : ℕ) (ha0 : 0 < a) (hab : a < b) (hbc : b < c)
    (ha : Even a) (hb : Even b) (hc : Even c)
    (hA : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ a ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ a)))
    (hB : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ b ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ b)))
    (hC : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ c ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ c)))
    {z : FullOverlapLawArray} (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    (∀ᵐ w ∂(z 2 : Measure (FullOverlapCoordinates 2)),
      w 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) ∧
    (z 2 : Measure (FullOverlapCoordinates 2)).real {w | |w 0 1| = Q} = 1 - x := by
  exact pair_law_support_and_mass_of_three_even_moments _
    ((physicalFullAsymptoticLimitSet_cube μ β hz) 2) x Q hQ
    a b c ha0 hab hbc ha hb hc
    (asymptoticPairPower_eq_of_physical_tendsto μ β _ a hA hz)
    (asymptoticPairPower_eq_of_physical_tendsto μ β _ b hB hz)
    (asymptoticPairPower_eq_of_physical_tendsto μ β _ c hC hz)

end SlowEquilibration.PureCapturePhysicalThreeEvenPairLaw
