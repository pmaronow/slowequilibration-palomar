-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPureMarkedValueWeight
public import SlowEquilibration.SphericalTAPPurePalmSourceUpper
public import SlowEquilibration.SphericalTAPPurePalmDeterminantQuadraticReduction
public import SlowEquilibration.SphericalPureLocalMaxPhysicalIntensity

@[expose] public section

/-! The literal pure value-conditioned determinant-weighted band mark
transfers into physical-energy Kac--Rice with the exact one-dimensional
Jacobian. -/

namespace SlowEquilibration.SphericalTAPPureMarkedEnergyPalmBound
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalMarkedWindows SphericalTAPMixedLowSumMarkedKR
open SphericalTAPPureMarkedValueWeight SphericalTAPPurePalmSourceUpper
open SphericalTAPPurePalmDeterminantQuadraticReduction
open SphericalSequentialRegression SphereHessian
open ConditionedDeterminantMoments GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A fixed-value upper bound on the genuine pure energy-Palm ratio bounds
the true value-conditioned Kac--Rice mark, with its sharp Hessian mean. -/
theorem pure_band_mark_local_intensity_le
    (d p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (β q b e : ℝ)
    (hk : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q) <
      (p:ℝ)*e)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hInt : let μ := FiniteMixture.pure p hp alpha halpha
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b))))
        (pureLaw p hp alpha halpha Q u hu e))
    (B : ℝ) (hB : 0 ≤ B)
    (hPalm : sourcePureEnergyPalmBandExpectation d p hp alpha halpha
      Q β e q b u hu ≤ B) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
      sourceMixedBandMark d μ β q b J u ∂valueConditionedLaw c u hu e) ≤
    ENNReal.ofReal B * ENNReal.ofReal
      (physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e)) := by
  dsimp only at hInt ⊢
  let μ := FiniteMixture.pure p hp alpha halpha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let D := intrinsicDet μ Q u
  let Z := fun J : Disorder (d+2) μ.maxDegree =>
    partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Icc (q-b) (q+b)))
  let num := ∫ J, D J*Z J ∂ν
  let den := ∫ J, D J ∂ν
  have hD (J : Disorder (d+2) μ.maxDegree) : 0 ≤ D J := abs_nonneg _
  have hZ (J : Disorder (d+2) μ.maxDegree) : 0 ≤ Z J := by
    dsimp [Z]
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hnum : 0 ≤ num := integral_nonneg (fun J => mul_nonneg (hD J) (hZ J))
  have hdeneq : den = physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) := by
    dsimp [den,ν,D]
    exact determinant_mean_eq_of_law
      (pure_intrinsicDet_hasLaw p hp alpha halpha hQ u hu e)
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hden : 0 < den := by
    rw [hdeneq]
    exact physicalMean_pos d 1 hb hk
  have hNumLe : num ≤ B*den := by
    have hh := (div_le_iff₀ hden).mp hPalm
    simpa only [sourcePureEnergyPalmBandExpectation,num,den,ν,D,Z,μ] using hh
  have hli :
      (∫⁻ J, ENNReal.ofReal (D J) * ENNReal.ofReal (Z J) ∂ν) =
        ENNReal.ofReal num := by
    calc
      _ = ∫⁻ J, ENNReal.ofReal (D J*Z J) ∂ν := by
        apply lintegral_congr
        intro J
        exact (ENNReal.ofReal_mul (hD J)).symm
      _ = ENNReal.ofReal num :=
        (ofReal_integral_eq_lintegral_ofReal hInt
          (.of_forall (fun J => mul_nonneg (hD J) (hZ J)))).symm
  rw [← pureLaw_eq_valueConditionedLaw p hp alpha halpha Q u hu e]
  change (∫⁻ J, ENNReal.ofReal (D J) * ENNReal.ofReal (Z J) ∂ν) ≤
    ENNReal.ofReal B * ENNReal.ofReal
      (physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e))
  rw [hli,← hdeneq,← ENNReal.ofReal_mul hB]
  exact ENNReal.ofReal_le_ofReal hNumLe

/-- The original pure critical-point band sum is bounded by the ordinary
physical all-critical energy density times the fixed-energy pure Palm band. -/
theorem actual_pure_band_sum_le_energy_palm_envelope
    (d p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (β q b : ℝ)
    (I : Set ℝ) (hI : MeasurableSet I) (B : ℝ → ℝ)
    (hEdge : ∀ H ∈ I,
      2*Real.sqrt (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q) <
        (p:ℝ)*(H/(d+2:ℕ)))
    (hB : ∀ H ∈ I, 0 ≤ B H)
    (hInt : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)), ∀ H ∈ I,
      let μ := FiniteMixture.pure p hp alpha halpha
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b))))
        (pureLaw p hp alpha halpha Q u hu (H/(d+2:ℕ))))
    (hPalm : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)), ∀ H ∈ I,
      sourcePureEnergyPalmBandExpectation d p hp alpha halpha Q β
        (H/(d+2:ℕ)) q b u hu ≤ B H) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (d+1) c
      (physicalEnergyWindow (d+2) I univ)
      (sourceMixedBandMark d μ β q b) J
      ∂disorderLaw (d+2) μ.maxDegree) ≤
    ∫⁻ H in I, pureCriticalPhysicalIntensity d p hp alpha halpha Q H *
      ENNReal.ofReal (B H) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let N : ℝ := (d+2:ℕ)
  have hW : pureScoreWindow p (physicalEnergyWindow (d+2) I univ) =
      (fun e : ℝ => N*e) ⁻¹' I := by
    ext e
    simp [pureScoreWindow,physicalEnergyWindow,rectangularScoreWindow,pureScoreLine,N]
  have hWm : MeasurableSet ((fun e : ℝ => N*e) ⁻¹' I) :=
    hI.preimage (measurable_const_mul _)
  have hCount (J : Disorder (d+2) μ.maxDegree) :
      actualScoreWindowCount (d+1) c (physicalEnergyWindow (d+2) I univ)
          (sourceMixedBandMark d μ β q b) J =
      actualValueWindowCount (d+1) c ((fun e : ℝ => N*e) ⁻¹' I)
          (sourceMixedBandMark d μ β q b) J := by
    rw [actual_pure_scoreWindowCount_eq_valueWindowCount
      (d+1) p hp alpha halpha Q _ _ J,hW]
  have hCountIntegral := lintegral_congr
    (μ := disorderLaw (d+2) μ.maxDegree) (fun J => hCount J)
  rw [hCountIntegral]
  have hKR := actual_pure_marked_count_le_value_weight
    d p hp alpha halpha hQ ((fun e : ℝ => N*e) ⁻¹' I) hWm
    (sourceMixedBandMark d μ β q b)
    (sourceMixedBandMark_measurable d μ β q b)
    (fun e => ENNReal.ofReal (B (N*e)))
    (by
      intro u hu e he
      exact pure_band_mark_local_intensity_le d p hp alpha halpha hQ
        β q b e (by
          have hNe : N*e ∈ I := he
          have hEq : (N*e)/(d+2:ℕ) = e := by
            dsimp [N]
            field_simp
          simpa only [hEq] using hEdge (N*e) hNe)
        u hu (by
          have hNe : N*e ∈ I := he
          have hEq : (N*e)/(d+2:ℕ) = e := by
            dsimp [N]
            field_simp
          simpa only [hEq] using hInt u hu (N*e) hNe)
        (B (N*e)) (hB (N*e) he) (by
          have hNe : N*e ∈ I := he
          have hEq : (N*e)/(d+2:ℕ) = e := by
            dsimp [N]
            field_simp
          simpa only [hEq] using hPalm u hu (N*e) hNe))
  calc
    _ ≤ ∫⁻ e in (fun e : ℝ => N*e) ⁻¹' I,
        pureCriticalIntensity d p hp alpha halpha Q e *
          ENNReal.ofReal (B (N*e)) := hKR
    _ = ∫⁻ H in I, pureCriticalPhysicalIntensity d p hp alpha halpha Q H *
          ENNReal.ofReal (B H) := by
      rw [setLIntegral_positive_rescale N (by dsimp [N]; positivity)]
      apply lintegral_congr
      intro H
      simp only [pureCriticalPhysicalIntensity,N]
      have hresc : ((d+2:ℕ):ℝ)*(H/(d+2:ℕ))=H := by
        field_simp
      rw [hresc]
      ac_rfl

end
end SlowEquilibration.SphericalTAPPureMarkedEnergyPalmBound
