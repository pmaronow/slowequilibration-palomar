-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPhysicalAngularSlice
public import SlowEquilibration.SphericalTAPLatitudeLIntegralChange

@[expose] public section

/-! The exact coarea/Fubini bridge for the source's symmetric latitude
averaging lemma. The angular lower bound is transferred to the genuine
restricted spherical Gibbs partition, with its correct latitude
normalizer and transverse entropy. -/

namespace SlowEquilibration.SphericalTAPPhysicalBandCoarea
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
open SlowEquilibration.SphericalTAPPhysicalAngularSlice
open SlowEquilibration.SphericalTAPLatitudeLIntegralChange
set_option autoImplicit false

/-- Joint integrability supplies both ordinary real integrals needed by
physical angular Fubini and the coarea conversion. -/
theorem physicalBand_integrable_slices
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (β center width : ℝ) (hwidth : 0 ≤ width)
    (hbelow : -1 < center-width) (habove : center+width < 1)
    (hjoint : Integrable
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)))
      ((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n))) :
    IntegrableOn
        (latitudeDensityPartition n β (field (mixtureCoefficients μ) J) u)
        (Icc (center-width) (center+width)) volume ∧
      Integrable (fun x : Vector n =>
        ∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u
            (physicalTransverseAt n u x) J β a)) (sphereLaw n) := by
  have horder : center-width ≤ center+width := by linarith
  constructor
  · apply hjoint.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact physicalAngularExponent_integral_eq_latitudeDensity n hn μ u J β a
      ⟨lt_of_lt_of_le hbelow ha.1, lt_of_le_of_lt ha.2 habove⟩
  · apply hjoint.integral_prod_right.congr
    exact Filter.Eventually.of_forall (fun x => by
      dsimp
      rw [intervalIntegral.integral_of_le horder,
        ← integral_Icc_eq_integral_Ioc])

/-- Deterministic physical form of the symmetric-band lower bound. The
only remaining premises are the source's curvature event and ordinary
integrability of the positive finite-band kernel. -/
theorem physicalBand_partition_lower
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (J : Disorder (n+1) μ.maxDegree)
    {r center width β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hwidth : 0 < width)
    (hβ : 0 ≤ β) (hC₀ : 0 ≤ C₀)
    (hinside : ∀ a ∈ Icc (center-width) (center+width), |a| ≤ r)
    (hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a,
      a ∈ Icc (center-width) (center+width) →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C₀*((n+1:ℕ):ℝ))
    (hjoint : Integrable
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)))
      ((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n))) :
    (latitudeNormalization n).toReal *
      ((2*width*Real.exp (-(((n+1:ℕ):ℝ)*
        (β*C₀+2/(1-r^2)^2))*width^2/2))*
        latitudeDensityPartition n β (field (mixtureCoefficients μ) J) u center) ≤
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (center-width) (center+width))) := by
  have hbelow : -1 < center-width := by
    have ha := hinside (center-width) ⟨le_refl _, by linarith [hwidth]⟩
    rw [abs_le] at ha
    linarith [hr1]
  have habove : center+width < 1 := by
    have ha := hinside (center+width) ⟨by linarith [hwidth], le_refl _⟩
    rw [abs_le] at ha
    linarith [hr1]
  have hint := physicalBand_integrable_slices n (by omega) μ u J β center width
    hwidth.le hbelow habove hjoint
  have hcoarea := partitionOn_symmetric_band_eq_real_integral hn β
    (field_contDiff (mixtureCoefficients μ) J).continuous u hu
    hwidth.le hbelow habove hint.1
  have hangular := physicalAngularBand_integral_eq_density n (by omega)
    μ u J β center width hwidth.le hbelow habove hjoint
  have hcentral := physicalAngularExponent_integrable n (by omega) μ u J β center
  have hlower := physicalAngularShell_lower_supported n hn μ u J hr0 hr1 hwidth hβ hC₀
    hinside hfield hcentral hint.2
  calc
    _ ≤ (latitudeNormalization n).toReal *
        (∫ x : Vector n, (∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u
            (physicalTransverseAt n u x) J β a)) ∂sphereLaw n) :=
      mul_le_mul_of_nonneg_left hlower ENNReal.toReal_nonneg
    _ = _ := by rw [hangular, hcoarea]

/-- The source's microscopic width `N⁻¹ᐟ²` cancels the dimensional
curvature factor. This gives an `N`-independent exponential loss and the
literal `2/√N` prefactor in the printed symmetric-latitude lemma. -/
theorem physicalMicroscopicBand_partition_lower
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (J : Disorder (n+1) μ.maxDegree)
    {r center β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hβ : 0 ≤ β) (hC₀ : 0 ≤ C₀)
    (hinside : ∀ a ∈ Icc
      (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
      (center+1/Real.sqrt (((n+1:ℕ):ℝ))), |a| ≤ r)
    (hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a, a ∈ Icc
      (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
      (center+1/Real.sqrt (((n+1:ℕ):ℝ))) →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C₀*((n+1:ℕ):ℝ))
    (hjoint : Integrable
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)))
      ((volume.restrict (Icc
        (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (center+1/Real.sqrt (((n+1:ℕ):ℝ))))).prod (sphereLaw n))) :
    (latitudeNormalization n).toReal *
      ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
        Real.exp (-(β*C₀+2/(1-r^2)^2)/2) *
        (Real.sqrt (1-center^2))^(n-2) *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) center) β
          (field (mixtureCoefficients μ) J)) ≤
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc
          (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
          (center+1/Real.sqrt (((n+1:ℕ):ℝ))))) := by
  have hN : 0 < (((n+1:ℕ):ℝ)) := by positivity
  have hsqrt : 0 < Real.sqrt (((n+1:ℕ):ℝ)) := Real.sqrt_pos.mpr hN
  have hwidth : 0 < 1/Real.sqrt (((n+1:ℕ):ℝ)) := one_div_pos.mpr hsqrt
  have hsq : (1/Real.sqrt (((n+1:ℕ):ℝ)))^2 =
      1/(((n+1:ℕ):ℝ)) := by
    rw [div_pow, one_pow, Real.sq_sqrt hN.le]
  have hfactor :
      2*(1/Real.sqrt (((n+1:ℕ):ℝ)))*
        Real.exp (-(((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2))*
          (1/Real.sqrt (((n+1:ℕ):ℝ)))^2/2) =
      (2/Real.sqrt (((n+1:ℕ):ℝ))) *
        Real.exp (-(β*C₀+2/(1-r^2)^2)/2) := by
    rw [hsq]
    have hNne : (((n+1:ℕ):ℝ)) ≠ 0 := ne_of_gt hN
    have he : -(((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2))*
        (1/(((n+1:ℕ):ℝ)))/2 =
        -(β*C₀+2/(1-r^2)^2)/2 := by
      field_simp
    rw [he]
    ring
  have h := physicalBand_partition_lower n hn μ u hu J hr0 hr1 hwidth
    hβ hC₀ hinside hfield hjoint
  rw [hfactor] at h
  simpa only [latitudeDensityPartition, mul_assoc] using h

end
end SlowEquilibration.SphericalTAPPhysicalBandCoarea
