-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticBankDeterminantHolder
public import SlowEquilibration.SphericalTAPMixedPalmLatitudeMeasurable
public import SlowEquilibration.ConditionedDeterminantMoments

@[expose] public section

/-! The actual mixed-posterior Hessian determinant has the normalized L²
bound needed for the source quadratic-bank Cauchy step. The remaining input
is precisely the second moment of the correlated quadratic latitude field. -/

namespace SlowEquilibration.SphericalTAPMixedPalmDeterminantQuadraticReduction
noncomputable section
open MeasureTheory ProbabilityTheory Filter SphericalModel
open ConditionedDeterminantMoments SphericalQuadraticBankDeterminantHolder
open SphericalTAPMixedPalmLatitudeMeasurable
open scoped Topology
set_option autoImplicit false
-- The conditioned coefficient kernel carries a proof-valued probability
-- instance under a local abbreviation for the posterior measure.
set_option linter.style.haveILetI false

/-- The genuine conditioned determinant and any quadratic bank with a
normalized second-moment bound have an integrable product. The determinant
constant comes from its already-proved physical GOE law. -/
theorem mixed_determinant_quadratic_bank_cauchy_eventually
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) {g : ℝ} (hg : 0 < g) :
    let K := (2 : ℝ)^2 * Real.exp
      (4*(Q^2*μ.xi2 Q)*(2 : ℝ)^2/g^2)
    ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
        (z : EuclideanSpace ℝ (Fin 2)),
        2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 →
        ∀ (Z₂ : Disorder (n+2) μ.maxDegree → ℝ)
          {m C : ℝ}, 0 < m →
          (∀ J, 0 ≤ Z₂ J) → Measurable Z₂ →
          Integrable (fun J => (Z₂ J/m)^2) (mixedLaw μ Q u hu z) →
          (∫ J, (Z₂ J/m)^2 ∂mixedLaw μ Q u hu z) ≤ C →
          let d := ∫ J, intrinsicDet μ Q u J ∂mixedLaw μ Q u hu z
          Integrable (fun J => intrinsicDet μ Q u J * Z₂ J)
            (mixedLaw μ Q u hu z) ∧
          (∫ J, intrinsicDet μ Q u J * Z₂ J
            ∂mixedLaw μ Q u hu z) ≤
            d*m*Real.sqrt K*Real.sqrt C := by
  have hdet := mixed_conditioned_determinant_moments_sharp_eventually
    μ hQ hnp hg
  filter_upwards [hdet] with n hn
  intro u hu z hz Z₂ m C hm hZ₀ hZm hZint hZbound
  let ν := mixedLaw μ Q u hu z
  let D := intrinsicDet μ Q u
  let d := ∫ J, D J ∂ν
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν,mixedLaw]
    infer_instance
  obtain ⟨_, _, hd, hDint, hDbound⟩ := hn u hu z hz 2 (by norm_num)
  have hDmeas : Measurable D := by
    unfold D intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (SphericalGaussianJet.centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hDlp : MemLp (fun J => D J/d) 2 ν :=
    (memLp_two_iff_integrable_sq (hDmeas.div_const d).aestronglyMeasurable).mpr
      (by simpa only [Real.rpow_two, D, d, ν] using hDint)
  have hZlp : MemLp (fun J => Z₂ J/m) 2 ν :=
    (memLp_two_iff_integrable_sq (hZm.div_const m).aestronglyMeasurable).mpr hZint
  exact determinant_quadratic_bank_cauchy ν D Z₂ hd hm
    (fun J => abs_nonneg _) hZ₀ hDlp hZlp
    (by simpa only [Real.rpow_two, D, d, ν] using hDbound) hZbound

end
end SlowEquilibration.SphericalTAPMixedPalmDeterminantQuadraticReduction
