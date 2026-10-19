-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPhysicalBandCoarea

@[expose] public section

/-! Automatic finite-band integrability of the actual physical latitude
exponential on the compact latitude and transverse sphere support. -/

namespace SlowEquilibration.SphericalTAPPhysicalBandIntegrability
noncomputable section
open MeasureTheory Set Metric
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
open SlowEquilibration.SphericalTAPPhysicalAngularSlice
open SlowEquilibration.SphericalTAPPhysicalBandCoarea
open SlowEquilibration.SphericalTAPLatitudeEntropyCurvature
set_option autoImplicit false

/-- On every strictly interior band the two-variable physical coarea
exponential is integrable under restricted Lebesgue measure times the
actual normalized transverse sphere law. -/
theorem physicalAngularBand_joint_integrable
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (β center width : ℝ)
    (hbelow : -1 < center-width) (habove : center+width < 1) :
    Integrable
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)))
      ((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n)) := by
  let K : Set (ℝ × Vector n) :=
    Icc (center-width) (center+width) ×ˢ closedBall 0 (Real.sqrt (n:ℝ))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hbase : ContinuousOn (fun p : ℝ × Vector n => 1-p.1^2) K := by
    fun_prop
  have hlog : ContinuousOn (fun p : ℝ × Vector n => Real.log (1-p.1^2)) K :=
    hbase.log (by
      intro p hp
      have ha : p.1 ∈ Icc (center-width) (center+width) := hp.1
      have hlo : -1 < p.1 := lt_of_lt_of_le hbelow ha.1
      have hhi : p.1 < 1 := lt_of_le_of_lt ha.2 habove
      have hh : 0 < 1-p.1^2 := by nlinarith
      exact hh.ne')
  have hf := (field_contDiff (mixtureCoefficients μ) J).continuous
  have hcont : ContinuousOn
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a))) K := by
    unfold Function.uncurry physicalLatitudeExponent latitudeExponent baseEntropy
      physicalLatitudeSlice physicalTransverseAt
    fun_prop
  have hsupp : ∀ᵐ p : ℝ × Vector n
      ∂((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n)),
      p ∈ K := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      filter_upwards [sphereLaw_support hn] with x hx
      refine ⟨ha, ?_⟩
      simp only [mem_closedBall, dist_zero_right]
      rw [← hx, Real.sqrt_sq (norm_nonneg x)]
    · exact measurableSet_Icc.prod measurableSet_closedBall
  have hint : IntegrableOn
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a))) K
      ((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n)) :=
    hcont.integrableOn_compact hK
  change Integrable _
    (((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n)).restrict K)
    at hint
  rwa [Measure.restrict_eq_self_of_ae_mem hsupp] at hint

/-- The microscopic symmetric-latitude lower bound with all finite-band
integrability proved internally. Its only analytic hypothesis is the
manuscript's physical Hamiltonian curvature event. -/
theorem physicalMicroscopicBand_partition_lower_of_curvature
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
        C₀*((n+1:ℕ):ℝ)) :
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
  have hwidth : 0 < 1/Real.sqrt (((n+1:ℕ):ℝ)) := by
    apply one_div_pos.mpr
    apply Real.sqrt_pos.mpr
    positivity
  have hbelow : -1 < center-1/Real.sqrt (((n+1:ℕ):ℝ)) := by
    have ha := hinside (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
      ⟨le_refl _, by linarith [hwidth]⟩
    rw [abs_le] at ha
    linarith [hr1]
  have habove : center+1/Real.sqrt (((n+1:ℕ):ℝ)) < 1 := by
    have ha := hinside (center+1/Real.sqrt (((n+1:ℕ):ℝ)))
      ⟨by linarith [hwidth], le_refl _⟩
    rw [abs_le] at ha
    linarith [hr1]
  exact physicalMicroscopicBand_partition_lower n hn μ u hu J hr0 hr1
    hβ hC₀ hinside hfield
    (physicalAngularBand_joint_integrable n (by omega) μ u J β center
      (1/Real.sqrt (((n+1:ℕ):ℝ))) hbelow habove)

/-- The transverse entropy power expressed in the manuscript's `s` form. -/
theorem sqrt_pow_eq_source_entropy (s : ℝ) (hs : 0 ≤ s) (m : ℕ) :
    (Real.sqrt s)^m = s^((m:ℝ)/2) := by
  calc
    (Real.sqrt s)^m = (s^(1/2:ℝ))^m := by rw [Real.sqrt_eq_rpow]
    _ = s^((1/2:ℝ)*(m:ℝ)) := (Real.rpow_mul_natCast hs (1/2) m).symm
    _ = s^((m:ℝ)/2) := by congr 1; ring

/-- Source-shaped symmetric latitude averaging on any physical band `I`
containing the microscopic central interval. The exact source entropy
`s^((N-3)/2)` appears as a real power, with `s=1-center²`. -/
theorem physicalSymmetricLatitudeAveraging_source
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (J : Disorder (n+1) μ.maxDegree)
    (I : Set ℝ) {r center β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hβ : 0 ≤ β) (hC₀ : 0 ≤ C₀)
    (hband : Icc
      (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
      (center+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I)
    (hIinside : ∀ a ∈ I, |a| ≤ r)
    (hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a, a ∈ I →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C₀*((n+1:ℕ):ℝ)) :
    (latitudeNormalization n).toReal *
      ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
        Real.exp (-(β*C₀+2/(1-r^2)^2)/2) *
        (1-center^2)^((((n-2:ℕ):ℝ))/2) *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) center) β
          (field (mixtureCoefficients μ) J)) ≤
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) := by
  have hwidth : 0 < 1/Real.sqrt (((n+1:ℕ):ℝ)) := by
    apply one_div_pos.mpr
    apply Real.sqrt_pos.mpr
    positivity
  have hcenter : center ∈ I := hband
    ⟨by linarith [hwidth], by linarith [hwidth]⟩
  have hs : 0 ≤ 1-center^2 := by
    have hc := hIinside center hcenter
    rw [abs_le] at hc
    nlinarith [hc.1, hc.2, hr0, hr1]
  have hpow := sqrt_pow_eq_source_entropy (1-center^2) hs (n-2)
  have hmicro := physicalMicroscopicBand_partition_lower_of_curvature n hn μ u hu J
    hr0 hr1 hβ hC₀ (fun a ha => hIinside a (hband ha))
    (fun x hx a ha => hfield x hx a (hband ha))
  have hsub : overlapRegion u (Icc
      (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
      (center+1/Real.sqrt (((n+1:ℕ):ℝ)))) ⊆ overlapRegion u I := by
    intro x hx
    exact hband hx
  have hmono : partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Icc
        (center-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (center+1/Real.sqrt (((n+1:ℕ):ℝ))))) ≤
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) := by
    exact setIntegral_mono_set
      (partition_integrand_integrable (by omega) β
        (field_contDiff (mixtureCoefficients μ) J).continuous).restrict
      (.of_forall fun _ => (Real.exp_pos _).le) (.of_forall hsub)
  rw [hpow] at hmicro
  exact hmicro.trans hmono

end
end SlowEquilibration.SphericalTAPPhysicalBandIntegrability
