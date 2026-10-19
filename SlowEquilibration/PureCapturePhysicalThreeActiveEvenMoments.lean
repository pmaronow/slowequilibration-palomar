-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairPolynomialExclusion
public import SlowEquilibration.PureCaptureThreeEvenMomentGap

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalThreeActiveEvenMoments

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalReplicaExclusionLimit PureCapturePhysicalFullArrayCubeSupport
open PureCaptureThreeEvenMomentGap
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem pairPower_integrable
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ z ∂ν, z ∈ fullOverlapCube 2) (p : ℕ) :
    Integrable (fun z : FullOverlapCoordinates 2 => (z 0 1) ^ p) ν := by
  have hc : Continuous (fun z : FullOverlapCoordinates 2 => (z 0 1) ^ p) := by fun_prop
  have hi := hc.continuousOn.integrableOn_compact (fullOverlapCube_compact 2) (μ := ν)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hcube] using hi

private theorem gap_integrable
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ z ∂ν, z ∈ fullOverlapCube 2) (a b c : ℕ) (Q : ℝ) :
    Integrable (fun z : FullOverlapCoordinates 2 => powerGap a b c (|z 0 1| / Q)) ν := by
  have hc : Continuous (fun z : FullOverlapCoordinates 2 =>
      powerGap a b c (|z 0 1| / Q)) := by unfold powerGap; fun_prop
  have hi := hc.continuousOn.integrableOn_compact (fullOverlapCube_compact 2) (μ := ν)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hcube] using hi

/-- The weighted Jensen gap is exactly a linear combination of the three
normalized physical even moments. -/
theorem gap_integral_eq_moments
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ z ∂ν, z ∈ fullOverlapCube 2)
    (a b c : ℕ) (ha : Even a) (hb : Even b) (hc : Even c) (Q : ℝ) :
    (∫ z, powerGap a b c (|z 0 1| / Q) ∂ν) =
      (1 - middleWeight a b c) * ((∫ z, (z 0 1) ^ a ∂ν) / Q ^ a) +
        middleWeight a b c * ((∫ z, (z 0 1) ^ c ∂ν) / Q ^ c) -
          ((∫ z, (z 0 1) ^ b ∂ν) / Q ^ b) := by
  have haI := (pairPower_integrable ν hcube a).div_const (Q ^ a)
  have hbI := (pairPower_integrable ν hcube b).div_const (Q ^ b)
  have hcI := (pairPower_integrable ν hcube c).div_const (Q ^ c)
  have hsum : Integrable (fun z : FullOverlapCoordinates 2 =>
      (1 - middleWeight a b c) * ((z 0 1) ^ a / Q ^ a) +
        middleWeight a b c * ((z 0 1) ^ c / Q ^ c)) ν :=
    (haI.const_mul _).add (hcI.const_mul _)
  simp_rw [powerGap, div_pow, ha.pow_abs, hb.pow_abs, hc.pow_abs]
  rw [integral_sub hsum hbI,
    integral_add (haI.const_mul (1 - middleWeight a b c))
      (hcI.const_mul (middleWeight a b c)),
    integral_const_mul, integral_const_mul,
    integral_div, integral_div, integral_div]

private theorem normalized_moment_tendsto
    (μ : FiniteMixture) (β x Q : ℝ) (hQ : Q ≠ 0) (p : ℕ)
    (hp : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ p))) :
    Tendsto (fun n : ℕ =>
      (∫ z, (z 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) / Q ^ p)
      atTop (𝓝 (1 - x)) := by
  simpa only [mul_div_cancel_right₀ _ (pow_ne_zero p hQ)] using hp.div_const (Q ^ p)

/-- Three arbitrary distinct even moments make the nonnegative Jensen gap
vanish in expectation; no arithmetic progression among the degrees is needed. -/
theorem physical_gap_integral_tendsto_zero
    (μ : FiniteMixture) (β x Q : ℝ) (hQ : 0 < Q)
    (a b c : ℕ) (ha : Even a) (hb : Even b) (hc : Even c)
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
      atTop (𝓝 ((1 - x) * Q ^ c))) :
    Tendsto (fun n : ℕ =>
      ∫ z, powerGap a b c (|z 0 1| / Q) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 0) := by
  have hAn := normalized_moment_tendsto μ β x Q hQ.ne' a hA
  have hBn := normalized_moment_tendsto μ β x Q hQ.ne' b hB
  have hCn := normalized_moment_tendsto μ β x Q hQ.ne' c hC
  have hh := ((hAn.const_mul (1 - middleWeight a b c)).add
    (hCn.const_mul (middleWeight a b c))).sub hBn
  have hzero : (1 - middleWeight a b c) * (1 - x) +
      middleWeight a b c * (1 - x) - (1 - x) = 0 := by ring
  rw [hzero] at hh
  convert hh using 1
  ext n
  exact gap_integral_eq_moments _ (physicalFullOverlapLaw_cube_ae μ β) a b c ha hb hc Q

/-- The manuscript's any-three-even-degrees Jensen argument yields actual
finite-volume exclusion of every strictly positive overlap other than Q. -/
theorem physical_pair_exclusion_of_three_active_even_moments
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
      atTop (𝓝 ((1 - x) * Q ^ c))) :
    ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := 2) μ β :
            Measure (FullOverlapCoordinates 2)) (fullEquilateralEvent 2 q ρ))
          atTop (𝓝 0) := by
  intro q hq hne
  obtain ⟨ρ, δ, hρ, hδ, hgap⟩ := exists_powerGap_neighborhood hab hbc hQ hq.1 hne
  refine ⟨ρ, hρ, ?_⟩
  have hlimit := physical_gap_integral_tendsto_zero μ β x Q hQ a b c ha hb hc hA hB hC
  let E := fullEquilateralEvent 2 q ρ
  have hreal : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)).real E) atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ =>
        (∫ z, powerGap a b c (|z 0 1| / Q) ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) / δ)
        atTop (𝓝 0) := by
      simpa only [zero_div] using hlimit.div_const δ
    apply squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hup
    let ν : Measure (FullOverlapCoordinates 2) := physicalFullOverlapLaw (n := n) (m := 2) μ β
    have hE : MeasurableSet E := (fullEquilateralEvent_open 2 q ρ).measurableSet
    have hg := gap_integrable ν (physicalFullOverlapLaw_cube_ae μ β) a b c Q
    have hbound := PureCapturePhysicalPairPolynomialExclusion.event_mass_mul_le_integral
      ν E hE _ hg δ hδ.le
      (.of_forall fun z => powerGap_nonneg ha0 hab hbc (div_nonneg (abs_nonneg _) hQ.le))
      (.of_forall fun z hz => hgap (z 0 1) (hz 0 1 (by decide)))
    exact (le_div_iff₀ hδ).2 (by simpa [ν, mul_comm] using hbound)
  have hENN := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  have hEq (n : ℕ) : ENNReal.ofReal
      ((physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)).real E) =
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)) E :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  simp only [Function.comp_def, ENNReal.ofReal_zero] at hENN
  simpa only [hEq, E] using hENN

end SlowEquilibration.PureCapturePhysicalThreeActiveEvenMoments
