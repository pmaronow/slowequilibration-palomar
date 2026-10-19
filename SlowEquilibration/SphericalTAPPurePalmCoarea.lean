-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureSourceQuadraticBound
public import SlowEquilibration.SphericalTAPMixedPalmLatitudeMeasurable

@[expose] public section

/-! Tonelli on the actual pure conditioned tensor law and the exact physical
latitude coarea measure.  The sole statistical premise is a bound on the
determinant-weighted latitude section. -/

namespace SlowEquilibration.SphericalTAPPurePalmCoarea
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPLatitudeLIntegralChange
open SphericalTAPMixedPalmLatitudeMeasurable
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A sectionwise determinant–latitude estimate integrates to the true
determinant-weighted physical band.  The angular law and Jacobian are
the ones obtained from spherical coarea. -/
theorem pure_weighted_band_lintegral_le_sections
    (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q β e : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    {q b : ℝ} (hb : 0 ≤ b) (hbelow : -1 < q-b) (habove : q+b < 1)
    (B : ℝ → ℝ≥0∞)
    (hsection : let μ := FiniteMixture.pure p hp alpha halpha
      ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          latitudeDensityPartition (d+1) β
            (field (mixtureCoefficients μ) J) u a)
        ∂pureLaw p hp alpha halpha Q u hu e) ≤ B a) :
    let μ := FiniteMixture.pure p hp alpha halpha
    (∫⁻ J, ENNReal.ofReal
      (intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b))))
      ∂pureLaw p hp alpha halpha Q u hu e) ≤
      latitudeNormalization (d+1) *
        (∫⁻ a in Icc (q-b) (q+b), B a ∂volume) := by
  dsimp only at hsection ⊢
  let μ := FiniteMixture.pure p hp alpha halpha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let A := Icc (q-b) (q+b)
  let D := intrinsicDet μ Q u
  let F := fun (J : Disorder (d+2) μ.maxDegree) (a : ℝ) =>
    latitudeDensityPartition (d+1) β
      (field (mixtureCoefficients μ) J) u a
  let : IsProbabilityMeasure ν := by
    dsimp [ν, pureLaw]
    infer_instance
  have hD : ∀ J, 0 ≤ D J := fun J => abs_nonneg _
  have hF : ∀ J a, 0 ≤ F J a :=
    fun J a => latitudeDensityPartition_nonneg (d+1) β _ u a
  have hcoarea (J : Disorder (d+2) μ.maxDegree) :
      ENNReal.ofReal (partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u A)) =
        latitudeNormalization (d+1) *
          ∫⁻ a in A, ENNReal.ofReal (F J a) ∂volume := by
    exact partitionOn_symmetric_band_eq_latitude (by omega) β
      (field_contDiff (mixtureCoefficients μ) J).continuous
      u hu hb hbelow habove
  have hm : Measurable (fun z : Disorder (d+2) μ.maxDegree × ℝ =>
      ENNReal.ofReal (D z.1 * F z.1 z.2)) := by
    exact (mixed_determinant_latitude_density_joint_measurable
      d μ Q u hu β).ennreal_ofReal
  have hFm (J : Disorder (d+2) μ.maxDegree) :
      Measurable (fun a : ℝ => ENNReal.ofReal (F J a)) := by
    have hP : Measurable (fun a : ℝ =>
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J)) :=
      (mixed_latitude_partition_joint_measurable d μ u β).comp
        (measurable_const.prodMk measurable_id)
    have hW : Measurable (fun a : ℝ => (Real.sqrt (1-a^2))^(d-1)) := by
      fun_prop
    exact (hW.mul hP).ennreal_ofReal
  have hInnerMeas : Measurable (fun J : Disorder (d+2) μ.maxDegree =>
      ∫⁻ a in A, ENNReal.ofReal (D J * F J a) ∂volume) :=
    hm.lintegral_prod_right'
  have hfact (J : Disorder (d+2) μ.maxDegree) :
      ENNReal.ofReal (D J) *
        (∫⁻ a in A, ENNReal.ofReal (F J a) ∂volume) =
      ∫⁻ a in A, ENNReal.ofReal (D J * F J a) ∂volume := by
    rw [← lintegral_const_mul _ (hFm J)]
    congr 1
    funext a
    exact (ENNReal.ofReal_mul (hD J)).symm
  have hMul (J : Disorder (d+2) μ.maxDegree) :
      ENNReal.ofReal (D J) *
        (latitudeNormalization (d+1) *
          ∫⁻ a in A, ENNReal.ofReal (F J a) ∂volume) =
      latitudeNormalization (d+1) *
        (ENNReal.ofReal (D J) *
          ∫⁻ a in A, ENNReal.ofReal (F J a) ∂volume) := by
    ac_rfl
  calc
    (∫⁻ J, ENNReal.ofReal
      (D J * partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u A)) ∂ν) =
        latitudeNormalization (d+1) *
          ∫⁻ J, ∫⁻ a in A,
            ENNReal.ofReal (D J * F J a) ∂volume ∂ν := by
      simp_rw [ENNReal.ofReal_mul (hD _), hcoarea]
      simp_rw [hMul, hfact]
      rw [lintegral_const_mul _ hInnerMeas]
      simp_rw [← ENNReal.ofReal_mul (hD _)]
      rfl
    _ = latitudeNormalization (d+1) *
          ∫⁻ a in A, ∫⁻ J,
            ENNReal.ofReal (D J * F J a) ∂ν ∂volume := by
      rw [lintegral_lintegral_swap]
      exact hm.aemeasurable
    _ ≤ latitudeNormalization (d+1) *
          ∫⁻ a in A, B a ∂volume := by
      have hinner : (∫⁻ a in A, ∫⁻ J,
            ENNReal.ofReal (D J * F J a) ∂ν ∂volume) ≤
          ∫⁻ a in A, B a ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
        exact hsection a ha
      gcongr

end
end SlowEquilibration.SphericalTAPPurePalmCoarea
