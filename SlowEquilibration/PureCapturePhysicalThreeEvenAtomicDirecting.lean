-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalThreeEvenDirectingNorm
public import SlowEquilibration.PureCapturePhysicalThreeEvenPairLaw
public import SlowEquilibration.PureCaptureAtomicDirectingGeometry

/-! The physical three even overlap moments imply countable atomic support for
almost every directing measure, with antipodal or orthogonal distinct atoms. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalThreeEvenAtomicDirecting

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionDirecting PureCaptureDirectingFullToScore
open PureCaptureRandomDirectingScoreArray PureCapturePhysicalThreeEvenPairLaw
open PureCapturePhysicalThreeEvenDirectingNorm PureCaptureAtomicDirectingGeometry
open GaussianReplicaKernel
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {Ξ H : Type*} [MeasurableSpace Ξ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The actual annealed overlap support transfers to almost every conditional
IID pair under a full directing representation. -/
theorem directing_pair_support_of_full_pair_support
    (R : RandomDirectingData Ξ H) (z : FullOverlapLawArray)
    (hrep : ∀ m, z m = directingDataFullLaw R m) (Q : ℝ)
    (hpair : ∀ᵐ w ∂(z 2 : Measure (FullOverlapCoordinates 2)),
      w 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) :
    ∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω,
      ∀ᵐ w ∂ R.directingKernel ω, (inner ℝ v w) ∈ ({-Q, 0, Q} : Set ℝ) := by
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hclosed : IsClosed ({-Q, 0, Q} : Set ℝ) := (Set.toFinite _).isClosed
  have hmeasFull : MeasurableSet {w : FullOverlapCoordinates 2 |
      w 0 1 ∈ ({-Q, 0, Q} : Set ℝ)} :=
    (hclosed.preimage (by fun_prop)).measurableSet
  rw [hrep 2] at hpair
  change ∀ᵐ w ∂Measure.map (directingFullOverlapCoordinates (H := H))
    (law R.disorderLaw R.directingKernel 2), w 0 1 ∈ ({-Q, 0, Q} : Set ℝ) at hpair
  have hfinite := (ae_map_iff
    directingFullOverlapCoordinates_continuous.measurable.aemeasurable hmeasFull).mp hpair
  have hfinite' : ∀ᵐ σ : Fin 2 → H ∂law R.disorderLaw R.directingKernel 2,
      (inner ℝ (σ 0) (σ 1)) ∈ ({-Q, 0, Q} : Set ℝ) := by
    simpa only [directingFullOverlapCoordinates, show (0 : Fin 2) ≠ 1 by decide, ite_false]
      using hfinite
  have hmeasPair : MeasurableSet {vw : H × H |
      (inner ℝ vw.1 vw.2) ∈ ({-Q, 0, Q} : Set ℝ)} :=
    (hclosed.preimage (by fun_prop)).measurableSet
  have hpairLaw : ∀ᵐ vw ∂((R.directingKernel ×ₖ R.directingKernel) ∘ₘ R.disorderLaw),
      (inner ℝ vw.1 vw.2) ∈ ({-Q, 0, Q} : Set ℝ) := by
    rw [← (pair_hasLaw R.disorderLaw R.directingKernel (0 : Fin 2) 1 (by decide)).map_eq]
    exact (ae_map_iff ((measurable_pi_apply 0).prodMk
      (measurable_pi_apply 1)).aemeasurable hmeasPair).mpr hfinite'
  filter_upwards [Measure.ae_ae_of_ae_comp hpairLaw] with ω hω
  rw [Kernel.prod_apply] at hω
  exact Measure.ae_ae_of_ae_prod hω

/-- The source atomic classification for every actual directing measure:
its support is countable, has full mass, consists of positive-mass norm-Q
atoms, and distinct atoms are antipodal or orthogonal. Pair support is
derived from the physical three-moment limits, not assumed. -/
theorem physical_directing_countable_atomic_support
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (CSParisiMeasure.variationalValue μ t)))
    (a b c : ℕ) (ha0 : 0 < a) (hab : a < b) (hbc : b < c)
    (ha : Even a) (hb : Even b) (hc : Even c)
    (hmoments : ∀ p ∈ ({a, b, c} : Finset ℕ),
      Tendsto (fun n : ℕ => ∫ w, (w 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
        atTop (𝓝 ((1 - x) * Q ^ p)))
    {z : FullOverlapLawArray} (hz : z ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H) (hrep : ∀ m, z m = directingDataFullLaw R m)
    (hball : ∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω, ‖v‖ ≤ 1) :
    ∀ᵐ ω ∂ R.disorderLaw,
      (R.directingKernel ω).support.Countable ∧
      R.directingKernel ω (R.directingKernel ω).support = 1 ∧
      (∀ v ∈ (R.directingKernel ω).support,
        0 < R.directingKernel ω {v} ∧ ‖v‖ ^ 2 = Q) ∧
      ∀ v ∈ (R.directingKernel ω).support, ∀ w ∈ (R.directingKernel ω).support,
        v ≠ w → w = -v ∨ (inner ℝ v w) = 0 := by
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hnorm := directing_norm_Q_of_three_even_physical_moments μ h hp
    a b c ha0 hab hbc ha hb hc hmoments hz R hrep hball
  have hpair := (asymptotic_pair_law_support_and_mass μ β x Q h.overlap_range.1
    a b c ha0 hab hbc ha hb hc (hmoments a (by simp))
    (hmoments b (by simp)) (hmoments c (by simp)) hz).1
  have hconditional := directing_pair_support_of_full_pair_support R z hrep Q hpair
  filter_upwards [hnorm, hconditional] with ω hn hpairs
  exact countable_atomic_support (R.directingKernel ω) h.overlap_range.1 hn hpairs

end SlowEquilibration.PureCapturePhysicalThreeEvenAtomicDirecting
