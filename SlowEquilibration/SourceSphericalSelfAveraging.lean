-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureParisiTemperatureEven
public import SlowEquilibration.PureCapturePhysicalPanchenkoUnconditionalEnergy
public import SlowEquilibration.PureCapturePhysicalThreeEvenSource

/-! Source `prop:dir-selfaveraging` and the Chen adapter for `prop:dir-even`.
The energy error is the literal original-disorder spherical Gibbs integral.
The active-degree limits and three-degree atomic classification use Chen's
explicit finite-mixture interface alone. The directing-family statements
use the repository's measurable probability kernels; the manuscript's more
general array-law-measurable families are not identified with such kernels.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSphericalSelfAveraging

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate SourceLiteratureParisi
open SourceLiteratureParisiTemperatureEven
open PureCapturePhysicalShellGG PureCapturePhysicalPanchenkoUnconditionalEnergy
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCaptureRandomDirectingScoreArray PureCapturePhysicalReplicaExclusionDirecting
open GaussianSpinInterpolation GaussianSpinComparison
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The printed `e_N = E ⟨H_N/N⟩`, in the original tensor disorder. -/
def sourceMeanEnergy (μ : FiniteMixture) (β : ℝ) (N : ℕ) : ℝ :=
  (∫ J : Disorder N μ.maxDegree,
    (∫ σ : Vector N, field (mixtureCoefficients μ) J σ
      ∂gibbsLaw N β (field (mixtureCoefficients μ) J))
    ∂disorderLaw N μ.maxDegree) / (N : ℝ)

/-- The printed `ε_N = E ⟨|H_N/N - e_N|⟩`, without a shell or a changed
disorder ensemble in its definition. -/
def sourceEpsilon (μ : FiniteMixture) (β : ℝ) (N : ℕ) : ℝ :=
  ∫ J : Disorder N μ.maxDegree,
    (∫ σ : Vector N,
      |field (mixtureCoefficients μ) J σ / (N : ℝ) - sourceMeanEnergy μ β N|
      ∂gibbsLaw N β (field (mixtureCoefficients μ) J))
    ∂disorderLaw N μ.maxDegree

private theorem original_integral_measurable (N : ℕ) (μ : FiniteMixture)
    (β e : ℝ) :
    Measurable (fun J : Disorder N μ.maxDegree =>
      ∫ σ : Vector N, |field (mixtureCoefficients μ) J σ - e|
        ∂gibbsLaw N β (field (mixtureCoefficients μ) J)) := by
  have hf : StronglyMeasurable (fun z : Disorder N μ.maxDegree × Vector N =>
      |field (mixtureCoefficients μ) z.1 z.2 - e|) :=
    ((field_jointContinuous (N := N) (mixtureCoefficients μ)).sub
      continuous_const).abs.stronglyMeasurable
  simpa only [allDimensionGibbsKernel_apply] using
    (hf.integral_kernel_prod_right' (κ := allDimensionGibbsKernel
      (N := N) (mixtureCoefficients μ) β)).measurable

private theorem shell_score_eq_original {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (g : EuclideanDisorder N μ.maxDegree) :
    parameterScore (shellLaw N) (shellLinear (mixtureCoefficients μ))
      (fun _ => true) g β =
    ∫ σ : Vector N, field (mixtureCoefficients μ) (unpackDisorder g) σ
      ∂gibbsLaw N β (field (mixtureCoefficients μ) (unpackDisorder g)) := by
  let _ : IsProbabilityMeasure (shellLaw N) := shellLaw_probability hN
  let L := shellLinear (N := N) (mixtureCoefficients μ)
  have hb : ∀ᵐ v ∂shellLaw N,
      ‖L v‖ ≤ Real.sqrt ((N : ℝ) * μ.xi 1) := by
    exact .of_forall fun v => by
      simpa only [L, covariancePolynomial_mixture] using
        shellLinear_bound hN (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) v
  have hmask : coordinateMask (fun _ : Coordinate N μ.maxDegree => true) true g = g := by
    ext i
    simp [coordinateMask, diagonal_apply]
  have heq : gibbsMeasure (shellLaw N) L
      (parameterOperator (fun _ => true) β g) =
    gibbsMeasure (shellLaw N) (parameterLinear L (fun _ => true) β) g := by
    apply gibbsMeasure_congr_field
    exact .of_forall fun v => rfl
  have hmap := shellGibbsLaw_map hN μ β g
  change score (shellLaw N) L (parameterOperator (fun _ => true) β g)
    (coordinateMask (fun _ => true) true g) = _
  rw [score_apply (shellLaw N) L (shellLinear_measurable _) hb,
    ← integral_gibbsMeasure (shellLaw N) L (shellLinear_measurable _) hb,
    hmask, heq, ← hmap,
    integral_map measurable_subtype_coe.aemeasurable
      (field_contDiff (mixtureCoefficients μ) (unpackDisorder g)).continuous.aestronglyMeasurable]
  exact integral_congr_ae (.of_forall fun v => sphereLinear_apply _ v.val g)

private theorem sourceMeanEnergy_eq_shell {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    sourceMeanEnergy μ β N =
      meanScore (shellLaw N) (shellLinear (mixtureCoefficients μ))
        (fun _ => true) β / (N : ℝ) := by
  have hf : Measurable (fun J : Disorder N μ.maxDegree =>
      ∫ σ : Vector N, field (mixtureCoefficients μ) J σ
        ∂gibbsLaw N β (field (mixtureCoefficients μ) J)) := by
    have hfield := (field_jointContinuous (N := N) (mixtureCoefficients μ)).stronglyMeasurable
    simpa only [allDimensionGibbsKernel_apply] using
      (hfield.integral_kernel_prod_right' (κ := allDimensionGibbsKernel
        (N := N) (mixtureCoefficients μ) β)).measurable
  have hint := (unpackDisorder_hasLaw N μ.maxDegree).integral_comp hf.aestronglyMeasurable
  unfold sourceMeanEnergy meanScore
  congr 1
  rw [← hint]
  exact integral_congr_ae (.of_forall fun g => (shell_score_eq_original hN μ β g).symm)

private theorem sourceEpsilon_eq_original {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    sourceEpsilon μ β N =
      (∫ g : EuclideanDisorder N μ.maxDegree,
        (∫ σ : Vector N,
          |field (mixtureCoefficients μ) (unpackDisorder g) σ -
            meanScore (shellLaw N) (shellLinear (mixtureCoefficients μ))
              (fun _ => true) β|
          ∂gibbsLaw N β (field (mixtureCoefficients μ) (unpackDisorder g)))
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) / (N : ℝ) := by
  unfold sourceEpsilon
  rw [sourceMeanEnergy_eq_shell hN μ β]
  simp_rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
    integral_div]
  congr 1
  exact ((unpackDisorder_hasLaw N μ.maxDegree).integral_comp
    (original_integral_measurable N μ β _).aestronglyMeasurable).symm

set_option linter.unusedVariables false in
/-- Source `prop:dir-selfaveraging` at every differentiability point of the
physical CS pressure limit. The dimension shift is removed in the conclusion. -/
theorem source_energy_self_averaging (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (hdiff : DifferentiableAt ℝ (CSParisiMeasure.variationalValue μ) β) :
    Tendsto (sourceEpsilon μ β) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 2).mp
  have hh := physical_original_sphere_energy_deviation_tendsto_zero μ β
    (CSParisiMeasure.variationalValue μ) (finite_pressure_limit_all_real_shift hChen μ) hdiff
  convert hh using 1
  funext n
  exact sourceEpsilon_eq_original (by omega : 1 ≤ n + 2) μ β

/-- In fact the unique CS minimizer supplies differentiability at every
temperature, so the Chen-conditional self-averaging needs no phase assumption. -/
theorem source_energy_self_averaging_all_positive (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) :
    Tendsto (sourceEpsilon μ β) atTop (𝓝 0) :=
  source_energy_self_averaging hChen μ hβ
    (CSVariationalTemperatureDerivative.variationalValue_hasDerivAt μ β).differentiableAt

/-- Source `prop:dir-even`(1), for every active degree, without a parity
restriction and conditional on Chen alone. -/
theorem source_active_degree_moments (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q) :
    ∀ p : Degree μ.maxDegree, 0 < mixtureCoefficients μ p →
      Tendsto (fun n : ℕ => ∫ w, (w 0 1) ^ p.val.val
        ∂(physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2))) atTop (𝓝 ((1 - x) * Q ^ p.val.val)) := by
  intro p hp
  exact SphericalActiveDegreeMomentFromParisi.physical_pairPower_tendsto_of_full_finiteMixture_parisi
    h h.beta_pos p hp (fun ν => finite_pressure_limit_all_real_shift hChen ν β)

/-- The exact source three-point support and total nonzero pair mass. -/
def ThreePointPairLaw (z : FullOverlapLawArray) (x Q : ℝ) : Prop :=
  (∀ᵐ w ∂(z 2 : Measure (FullOverlapCoordinates 2)),
    w 0 1 ∈ ({-Q, 0, Q} : Set ℝ)) ∧
  (z 2 : Measure (FullOverlapCoordinates 2)).real {w | |w 0 1| = Q} = 1 - x

/-- The literal countable measure sum, positive atoms, norm support, and
antipodal-or-orthogonal geometry printed in `prop:dir-even`(2). -/
def CountablyAtomicAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] (ν : Measure H) (Q : ℝ) : Prop :=
  ν = Measure.sum (fun v : ν.support => ν {(v : H)} • Measure.dirac (v : H)) ∧
  ν.support.Countable ∧ ν ν.support = 1 ∧
  (∀ v ∈ ν.support, 0 < ν {v} ∧ ‖v‖ ^ 2 = Q) ∧
  ∀ v ∈ ν.support, ∀ w ∈ ν.support, v ≠ w → w = -v ∨ inner ℝ v w = 0

/-- Source `prop:dir-even`(2) for every measurable directing kernel of
every physical overlap limit. Three active even degrees suffice, even when
additional active degrees are odd. No ground-state or Subag premise occurs. -/
theorem source_three_degree_directing
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (pa pb pc : Degree μ.maxDegree)
    (ha : Even pa.val.val) (hb : Even pb.val.val) (hc : Even pc.val.val)
    (hab : pa.val.val < pb.val.val) (hbc : pb.val.val < pc.val.val)
    (hca : 0 < mixtureCoefficients μ pa) (hcb : 0 < mixtureCoefficients μ pb)
    (hcc : 0 < mixtureCoefficients μ pc) {z : FullOverlapLawArray}
    (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    ThreePointPairLaw z x Q ∧
      ∀ R : RandomDirectingData Ξ H, (∀ m, z m = directingDataFullLaw R m) →
        (∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω, ‖v‖ ≤ 1) →
        ∀ᵐ ω ∂ R.disorderLaw, CountablyAtomicAt (R.directingKernel ω) Q :=
  PureCapturePhysicalThreeEvenSource.source_three_even_degrees_of_universal_parisi
    μ h (finite_pressure_limit_all_real_shift hChen) pa pb pc ha hb hc hab hbc hca hcb hcc hz

/-- The source atomic classification has an actual directing representation,
constructed by the proved physical Dovbysh--Sudakov theorem. -/
theorem source_three_degree_atomic_representation
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (pa pb pc : Degree μ.maxDegree)
    (ha : Even pa.val.val) (hb : Even pb.val.val) (hc : Even pc.val.val)
    (hab : pa.val.val < pb.val.val) (hbc : pb.val.val < pc.val.val)
    (hca : 0 < mixtureCoefficients μ pa) (hcb : 0 < mixtureCoefficients μ pb)
    (hcc : 0 < mixtureCoefficients μ pc) {z : FullOverlapLawArray}
    (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    ThreePointPairLaw z x Q ∧
      ∃ R : RandomDirectingData (ProbabilityMeasure OverlapPaper.DSHilbert)
          OverlapPaper.DSHilbert,
        (∀ m, z m = directingDataFullLaw R m) ∧
        ∀ᵐ ω ∂ R.disorderLaw, CountablyAtomicAt (R.directingKernel ω) Q :=
  PureCapturePhysicalThreeEvenSource.source_three_even_degrees_atomic_representation_of_universal_parisi
    μ h (finite_pressure_limit_all_real_shift hChen) pa pb pc ha hb hc hab hbc hca hcb hcc hz

private theorem three_active_even_degrees (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) (hcard : 3 ≤ μ.coeff.support.card) :
    ∃ pa pb pc : Degree μ.maxDegree,
      Even pa.val.val ∧ Even pb.val.val ∧ Even pc.val.val ∧
      pa.val.val < pb.val.val ∧ pb.val.val < pc.val.val ∧
      0 < mixtureCoefficients μ pa ∧ 0 < mixtureCoefficients μ pb ∧
      0 < mixtureCoefficients μ pc := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < μ.coeff.support.card)
  have hordered : ∃ a ∈ μ.coeff.support, ∃ b ∈ μ.coeff.support,
      ∃ c ∈ μ.coeff.support, a < b ∧ b < c := by
    rcases lt_or_gt_of_ne hab with hab | hba
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨a, ha, b, hb, c, hc, hab, hbc⟩
      · rcases lt_or_gt_of_ne hac with hac | hca
        · exact ⟨a, ha, c, hc, b, hb, hac, hcb⟩
        · exact ⟨c, hc, a, ha, b, hb, hca, hab⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨b, hb, a, ha, c, hc, hba, hac⟩
      · rcases lt_or_gt_of_ne hbc with hbc | hcb
        · exact ⟨b, hb, c, hc, a, ha, hbc, hca⟩
        · exact ⟨c, hc, b, hb, a, ha, hcb, hba⟩
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc⟩ := hordered
  let pa : Degree μ.maxDegree :=
    ⟨⟨a, Nat.lt_succ_of_le (μ.degree_bounds ha).2⟩, μ.degree_ge_two ha⟩
  let pb : Degree μ.maxDegree :=
    ⟨⟨b, Nat.lt_succ_of_le (μ.degree_bounds hb).2⟩, μ.degree_ge_two hb⟩
  let pc : Degree μ.maxDegree :=
    ⟨⟨c, Nat.lt_succ_of_le (μ.degree_bounds hc).2⟩, μ.degree_ge_two hc⟩
  exact ⟨pa, pb, pc, heven a ha, heven b hb, heven c hc, hab, hbc,
    μ.coeff_pos ha, μ.coeff_pos hb, μ.coeff_pos hc⟩

/-- The source's actual even-mixture and at-least-three-coefficients
hypotheses automatically supply the three degrees. The conclusion retains
both the universal kernel classification and an actual atomic representation. -/
theorem source_even_three_degree_directing
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (heven : ∀ p ∈ μ.coeff.support, Even p)
    (hcard : 3 ≤ μ.coeff.support.card) {z : FullOverlapLawArray}
    (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    ThreePointPairLaw z x Q ∧
      (∀ R : RandomDirectingData Ξ H, (∀ m, z m = directingDataFullLaw R m) →
        (∀ᵐ ω ∂ R.disorderLaw, ∀ᵐ v ∂ R.directingKernel ω, ‖v‖ ≤ 1) →
        ∀ᵐ ω ∂ R.disorderLaw, CountablyAtomicAt (R.directingKernel ω) Q) ∧
      ∃ R : RandomDirectingData (ProbabilityMeasure OverlapPaper.DSHilbert)
          OverlapPaper.DSHilbert,
        (∀ m, z m = directingDataFullLaw R m) ∧
        ∀ᵐ ω ∂ R.disorderLaw, CountablyAtomicAt (R.directingKernel ω) Q := by
  obtain ⟨pa, pb, pc, ha, hb, hc, hab, hbc, hca, hcb, hcc⟩ :=
    three_active_even_degrees μ heven hcard
  obtain ⟨hpair, hall⟩ := source_three_degree_directing (Ξ := Ξ) (H := H)
    hChen μ h pa pb pc ha hb hc hab hbc hca hcb hcc hz
  obtain ⟨_, hex⟩ := source_three_degree_atomic_representation
    hChen μ h pa pb pc ha hb hc hab hbc hca hcb hcc hz
  exact ⟨hpair, hall, hex⟩

end SlowEquilibration.SourceSphericalSelfAveraging
