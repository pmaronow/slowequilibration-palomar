-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalThreeEvenAtomicDirecting
public import SlowEquilibration.SphericalActiveDegreeMomentFromParisi

/-! Source `prop:dir-even`: three active even degrees give the physical pair
law and an atomic directing representation, conditional on the universal
physical Parisi formula. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalThreeEvenSource

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalTAPCertificate
open SphericalActiveDegreeMomentFromParisi
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionDirecting PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalThreeEvenPairLaw PureCapturePhysicalThreeEvenAtomicDirecting
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Source `prop:dir-even`, pair-law and directing-atom clauses, conditional
only on the still-open physical Parisi formula. The physical moments,
three-point support, exact nonzero mass, norm support, and atomic geometry
are all derived internally. Three active even degrees suffice even if other
active degrees of the mixture are odd. -/
theorem source_three_even_degrees_of_universal_parisi
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hparisi : ∀ (ν : FiniteMixture) (t : ℝ),
      Tendsto (fun n : ℕ => quenchedPressure (n+2) ν t)
        atTop (𝓝 (CSParisiMeasure.variationalValue ν t)))
    (pa pb pc : Degree μ.maxDegree)
    (ha : Even pa.val.val) (hb : Even pb.val.val) (hc : Even pc.val.val)
    (hab : pa.val.val < pb.val.val) (hbc : pb.val.val < pc.val.val)
    (hca : 0 < mixtureCoefficients μ pa)
    (hcb : 0 < mixtureCoefficients μ pb)
    (hcc : 0 < mixtureCoefficients μ pc)
    {z : FullOverlapLawArray} (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    ((∀ᵐ w ∂(z 2 : Measure (FullOverlapCoordinates 2)),
        w 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) ∧
      (z 2 : Measure (FullOverlapCoordinates 2)).real {w | |w 0 1| = Q} = 1 - x) ∧
    ∀ (R : RandomDirectingData Ξ H),
      (∀ m, z m = directingDataFullLaw R m) →
      (∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω, ‖v‖ ≤ 1) →
      ∀ᵐ ω ∂ R.disorderLaw,
        R.directingKernel ω = Measure.sum (fun v : (R.directingKernel ω).support =>
          R.directingKernel ω {(v : H)} • Measure.dirac (v : H)) ∧
        (R.directingKernel ω).support.Countable ∧
        R.directingKernel ω (R.directingKernel ω).support = 1 ∧
        (∀ v ∈ (R.directingKernel ω).support,
          0 < R.directingKernel ω {v} ∧ ‖v‖ ^ 2 = Q) ∧
        ∀ v ∈ (R.directingKernel ω).support, ∀ w ∈ (R.directingKernel ω).support,
          v ≠ w → w = -v ∨ inner ℝ v w = 0 := by
  have hA := physical_pairPower_tendsto_of_full_finiteMixture_parisi
    h h.beta_pos pa hca (fun ν => hparisi ν β)
  have hB := physical_pairPower_tendsto_of_full_finiteMixture_parisi
    h h.beta_pos pb hcb (fun ν => hparisi ν β)
  have hC := physical_pairPower_tendsto_of_full_finiteMixture_parisi
    h h.beta_pos pc hcc (fun ν => hparisi ν β)
  have ha0 : 0 < pa.val.val := by have hh := pa.property; omega
  have hmoments : ∀ p ∈ ({pa.val.val, pb.val.val, pc.val.val} : Finset ℕ),
      Tendsto (fun n : ℕ => ∫ w, (w 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
        atTop (𝓝 ((1 - x) * Q ^ p)) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC
  refine ⟨asymptotic_pair_law_support_and_mass μ β x Q h.overlap_range.1
    pa.val.val pb.val.val pc.val.val ha0 hab hbc ha hb hc hA hB hC hz, ?_⟩
  intro R hrep hball
  have hatomic := physical_directing_countable_atomic_support μ h (hparisi μ)
    pa.val.val pb.val.val pc.val.val ha0 hab hbc ha hb hc hmoments hz R hrep hball
  filter_upwards [hatomic] with ω hω
  exact ⟨PureCaptureAtomicDirectingGeometry.eq_sum_smul_dirac_support_of_countable
    (R.directingKernel ω) hω.1, hω⟩

/-- An actual atomic representation exists for every physical full-array
limit. The representation is obtained from the proved physical
Dovbysh--Sudakov theorem, so the preceding universal classification has
an inhabited representation class. -/
theorem source_three_even_degrees_atomic_representation_of_universal_parisi
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hparisi : ∀ (ν : FiniteMixture) (t : ℝ),
      Tendsto (fun n : ℕ => quenchedPressure (n+2) ν t)
        atTop (𝓝 (CSParisiMeasure.variationalValue ν t)))
    (pa pb pc : Degree μ.maxDegree)
    (ha : Even pa.val.val) (hb : Even pb.val.val) (hc : Even pc.val.val)
    (hab : pa.val.val < pb.val.val) (hbc : pb.val.val < pc.val.val)
    (hca : 0 < mixtureCoefficients μ pa)
    (hcb : 0 < mixtureCoefficients μ pb)
    (hcc : 0 < mixtureCoefficients μ pc)
    {z : FullOverlapLawArray} (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    ((∀ᵐ w ∂(z 2 : Measure (FullOverlapCoordinates 2)),
        w 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) ∧
      (z 2 : Measure (FullOverlapCoordinates 2)).real {w | |w 0 1| = Q} = 1 - x) ∧
    ∃ R : RandomDirectingData (ProbabilityMeasure OverlapPaper.DSHilbert)
        OverlapPaper.DSHilbert,
      (∀ m, z m = directingDataFullLaw R m) ∧
      ∀ᵐ ω ∂ R.disorderLaw,
        R.directingKernel ω = Measure.sum (fun v : (R.directingKernel ω).support =>
          R.directingKernel ω {(v : OverlapPaper.DSHilbert)} •
            Measure.dirac (v : OverlapPaper.DSHilbert)) ∧
        (R.directingKernel ω).support.Countable ∧
        R.directingKernel ω (R.directingKernel ω).support = 1 ∧
        (∀ v ∈ (R.directingKernel ω).support,
          0 < R.directingKernel ω {v} ∧ ‖v‖ ^ 2 = Q) ∧
        ∀ v ∈ (R.directingKernel ω).support, ∀ w ∈ (R.directingKernel ω).support,
          v ≠ w → w = -v ∨ inner ℝ v w = 0 := by
  obtain ⟨R, hrep, hball⟩ :=
    PureCapturePhysicalDSFiniteBridge.physicalFullAsymptoticLimit_randomDirecting μ β hz
  obtain ⟨hpair, hatomic⟩ := source_three_even_degrees_of_universal_parisi
    (Ξ := ProbabilityMeasure OverlapPaper.DSHilbert) (H := OverlapPaper.DSHilbert)
    μ h hparisi pa pb pc ha hb hc hab hbc hca hcb hcc hz
  exact ⟨hpair, R, hrep, hatomic R hrep hball⟩

end SlowEquilibration.PureCapturePhysicalThreeEvenSource
