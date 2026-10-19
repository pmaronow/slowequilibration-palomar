-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelDeterminantPalm
public import SlowEquilibration.SourcePureCapBorelPosteriorMeanRadial
public import SlowEquilibration.SphericalTAPPureMarkedValueWeight

/-! An arbitrary Borel cap partition as an actual original-field marked
Kac--Rice weight, with its uniform determinant-weighted Palm bound. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelMarkedValue
noncomputable section
open Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open PureStationarity ConditionedDeterminantMoments SphereHessian
open SourcePureCapBorelDeterminantPalm
open SourcePureCapBorelPosteriorMeanRadial
open SourcePureCapBorelRadialFirst
open SourcePureLatitudeRadialDisintegration
open SphericalTAPPurePalmDeterminantQuadraticReduction
open SphericalTAPPureMarkedValueWeight
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

def originalBorelBandMark (d : ℕ) (μ : FiniteMixture)
    (β : ℝ) (I : Set ℝ) (J : Disorder (d+2) μ.maxDegree)
    (u : Vector (d+2)) : ℝ≥0∞ :=
  ENNReal.ofReal (partitionOn β (field (mixtureCoefficients μ) J)
    (overlapRegion u I))

theorem originalBorelBandMark_measurable (d : ℕ) (μ : FiniteMixture)
    (β : ℝ) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
      originalBorelBandMark d μ β I z.1 z.2) := by
  simpa only [originalBorelBandMark,overlapRestrictedPartition,overlapRegion]
    using (overlapRestrictedPartition_measurable (N := d+2)
      (mixtureCoefficients μ) β hI).ennreal_ofReal

/-- The exact conditioned mark, including the original Hessian determinant,
is bounded by the pole-independent Borel radial mean times the GOE
determinant mean. -/
theorem pure_original_borel_band_mark_local_intensity
    (d p : ℕ) (hd : 1 ≤ d) (hp : 2 ≤ p) (β C : ℝ)
    (hC : 0 ≤ C)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hPalm : let μ := FiniteMixture.pure p hp 1 (by positivity)
      let c := centerCoefficients (mixtureCoefficients μ) 1
      let ν := valueConditionedLaw c u hu e
      let Z := fun J => partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I)
      let D := intrinsicDet μ 1 u
      Integrable (fun J => D J*Z J) ν ∧
        (∫ J, D J*Z J ∂ν) ≤ C*(∫ J, D J ∂ν)*(∫ J, Z J ∂ν)) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
      originalBorelBandMark d μ β I J u
      ∂valueConditionedLaw c u hu e) ≤
      (ENNReal.ofReal C *
        (∫⁻ s : Ioi (0:ℝ),
          radialMeanWeight (d+1) p β ((d+2:ℕ)*e) I s
          ∂radialLaw (d+1))) *
        ENNReal.ofReal (GOEPhysicalPotential.physicalMean d (d+2)
          (μ.xi2 1) ((p:ℝ)*e)) := by
  dsimp only at hPalm ⊢
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let ν := valueConditionedLaw c u hu e
  let D : Disorder (d+2) μ.maxDegree → ℝ := intrinsicDet μ 1 u
  let Z : Disorder (d+2) μ.maxDegree → ℝ := fun J =>
    partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I)
  let num := ∫ J, D J*Z J ∂ν
  let den := ∫ J, D J ∂ν
  let m := ∫ J, Z J ∂ν
  have hD₀ : ∀ J, 0 ≤ D J := fun _ => abs_nonneg _
  have hZ₀ : ∀ J, 0 ≤ Z J := by
    intro J
    dsimp [Z]
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hden : 0 ≤ den := integral_nonneg hD₀
  have hm : 0 ≤ m := integral_nonneg hZ₀
  have hdeneq : den = GOEPhysicalPotential.physicalMean d (d+2)
      (μ.xi2 1) ((p:ℝ)*e) := by
    have hLaw : pureLaw p hp 1 (by positivity) 1 u hu e = ν :=
      pureLaw_eq_valueConditionedLaw p hp 1 (by positivity) 1 u hu e
    dsimp [den,D]
    rw [←hLaw]
    simpa only [one_pow,one_mul] using
      (determinant_mean_eq_of_law
        (pure_intrinsicDet_hasLaw p hp 1 (by positivity)
          (Q := 1) (by positivity) u hu e))
  have hmeaneq : ENNReal.ofReal m =
      ∫⁻ s : Ioi (0:ℝ), radialMeanWeight (d+1) p β ((d+2:ℕ)*e) I s
        ∂radialLaw (d+1) := by
    have hh := pure_original_posterior_borel_mean_radial
      (d+1) p (by omega) hp β ((d+2:ℕ)*e) u
      (by simpa only [show d+1+1=d+2 by omega] using hu) hI
    have he : ((d+2:ℕ)*e)/(d+2:ℕ) = e := by field_simp
    simpa only [m,Z,ν,c,μ,he,show d+1+1=d+2 by omega] using hh
  have hli : (∫⁻ J, ENNReal.ofReal (D J)*ENNReal.ofReal (Z J) ∂ν) =
      ENNReal.ofReal num := by
    calc
      _ = ∫⁻ J, ENNReal.ofReal (D J*Z J) ∂ν := by
        apply lintegral_congr
        intro J
        exact (ENNReal.ofReal_mul (hD₀ J)).symm
      _ = ENNReal.ofReal num :=
        (ofReal_integral_eq_lintegral_ofReal hPalm.1
          (.of_forall (fun J => mul_nonneg (hD₀ J) (hZ₀ J)))).symm
  change (∫⁻ J, ENNReal.ofReal (D J)*ENNReal.ofReal (Z J) ∂ν) ≤
    (ENNReal.ofReal C *
      (∫⁻ s, radialMeanWeight (d+1) p β ((d+2:ℕ)*e) I s
        ∂radialLaw (d+1))) *
      ENNReal.ofReal (GOEPhysicalPotential.physicalMean d (d+2)
        (μ.xi2 1) ((p:ℝ)*e))
  rw [hli,←hmeaneq,←hdeneq]
  calc
    ENNReal.ofReal num ≤ ENNReal.ofReal (C*den*m) :=
      ENNReal.ofReal_le_ofReal hPalm.2
    _ = (ENNReal.ofReal C*ENNReal.ofReal m)*ENNReal.ofReal den := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC hden),ENNReal.ofReal_mul hC]
      ac_rfl

end
end SlowEquilibration.SourcePureCapBorelMarkedValue
