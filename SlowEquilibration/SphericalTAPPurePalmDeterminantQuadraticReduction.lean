-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmDeterminantQuadraticReduction
public import SlowEquilibration.SphericalQuadraticLatitudeJetPureCertificateSecondMoment

@[expose] public section

/-! The sharp conditioned pure determinant moment can be paired with any
nonnegative quadratic bank under the literal pure value-and-gradient Palm law. -/

namespace SlowEquilibration.SphericalTAPPurePalmDeterminantQuadraticReduction
noncomputable section
open MeasureTheory ProbabilityTheory Filter SphericalModel SphericalGaussianJet
open ConditionedDeterminantMoments SphericalQuadraticBankDeterminantHolder
open SphericalTAPMixedPalmLatitudeMeasurable SphericalMarkedWindows
open scoped Topology
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

theorem pureLaw_eq_valueConditionedLaw
    {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ)) (e : ℝ) :
    pureLaw p hp alpha halpha Q u hu e =
      valueConditionedLaw
        (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q)
        u hu e := by
  unfold pureLaw valueConditionedLaw
  congr 1

/-- The actual pure conditioned determinant has a sharp normalized L²
bound, so every nonnegative quadratic bank with its own L² bound has an
integrable determinant-weighted product under the genuine pure posterior. -/
theorem pure_determinant_quadratic_bank_cauchy_eventually
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let K := (2 : ℝ)^2 * Real.exp
      (4*(Q^2*μ.xi2 Q)*(2 : ℝ)^2/g^2)
    ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ)) (e : ℝ),
        2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*e →
        ∀ (Z₂ : Disorder (n+2) μ.maxDegree → ℝ)
          {m C : ℝ}, 0 < m →
          (∀ J, 0 ≤ Z₂ J) → Measurable Z₂ →
          Integrable (fun J => (Z₂ J/m)^2) (pureLaw p hp alpha halpha Q u hu e) →
          (∫ J, (Z₂ J/m)^2 ∂pureLaw p hp alpha halpha Q u hu e) ≤ C →
          let d := ∫ J, intrinsicDet μ Q u J ∂pureLaw p hp alpha halpha Q u hu e
          Integrable (fun J => intrinsicDet μ Q u J * Z₂ J)
            (pureLaw p hp alpha halpha Q u hu e) ∧
          (∫ J, intrinsicDet μ Q u J * Z₂ J
            ∂pureLaw p hp alpha halpha Q u hu e) ≤
              d*m*Real.sqrt K*Real.sqrt C := by
  have hdet := pure_conditioned_determinant_moments_sharp_eventually
    p hp alpha halpha hQ hg
  filter_upwards [hdet] with n hn
  intro u hu e he Z₂ m C hm hZ₀ hZm hZint hZbound
  let μ := FiniteMixture.pure p hp alpha halpha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let D := intrinsicDet μ Q u
  let d := ∫ J, D J ∂ν
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν,pureLaw]
    infer_instance
  obtain ⟨_, _, hd, hDint, hDbound⟩ := hn u hu e he 2 (by norm_num)
  have hDmeas : Measurable D := by
    unfold D intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hDlp : MemLp (fun J => D J/d) 2 ν :=
    (memLp_two_iff_integrable_sq (hDmeas.div_const d).aestronglyMeasurable).mpr
      (by simpa only [Real.rpow_two, D, d, ν, μ] using hDint)
  have hZlp : MemLp (fun J => Z₂ J/m) 2 ν :=
    (memLp_two_iff_integrable_sq (hZm.div_const m).aestronglyMeasurable).mpr hZint
  exact determinant_quadratic_bank_cauchy ν D Z₂ hd hm
    (fun J => abs_nonneg _) hZ₀ hDlp hZlp
    (by simpa only [Real.rpow_two, D, d, ν, μ] using hDbound) hZbound

end
end SlowEquilibration.SphericalTAPPurePalmDeterminantQuadraticReduction
