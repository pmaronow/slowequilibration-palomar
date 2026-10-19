-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureOriginalConditionalBandFubini

@[expose] public section

/-! The source `pc-band-mean` identity on a fixed closed latitude band.
The original disorder posterior, original Hamiltonian, and normalized
spherical coarea prefactor all appear literally. -/

namespace SlowEquilibration.SphericalPureOriginalConditionalBandCoarea
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalPureOriginalConditionalBandFubini
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPLatitudeLIntegralChange
set_option autoImplicit false

def originalPureEffectivePotential (n p : ℕ) (alpha β H : ℝ)
    (u w : Vector (n+1)) : ℝ :=
  β*H*(overlap u w)^p+
    (n+1 : ℕ)*β^2*sourcePureLatitudeVariance p alpha (overlap u w)/2

theorem originalPureEffectivePotential_continuous (n p : ℕ)
    (alpha β H : ℝ) (u : Vector (n+1)) :
    Continuous (originalPureEffectivePotential n p alpha β H u) := by
  unfold originalPureEffectivePotential overlap sourcePureLatitudeVariance
  fun_prop

theorem originalPureMeanProfile_eq_exp_effective (n p : ℕ) (alpha β H : ℝ)
    (u w : Vector (n+1)) :
    originalPureMeanProfile n p alpha β H u w =
      Real.exp (originalPureEffectivePotential n p alpha β H u w) := rfl

/-- On the actual latitude law, the effective field is constant. This is
where the posterior pointwise Gaussian mean meets spherical coarea. -/
theorem originalPureEffectivePotential_latitude_ae
    (n p : ℕ) (hn : 1 ≤ n) (alpha β H : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (q : ℝ) (hq : |q| ≤ 1) :
    ∀ᵐ w ∂latitudeLaw u (latitudeFrameAt u) q,
      originalPureEffectivePotential n p alpha β H u w =
        β*H*q^p+(n+1 : ℕ)*β^2*sourcePureLatitudeVariance p alpha q/2 := by
  filter_upwards [latitudeLaw_support hn u hu (latitudeFrameAt u)
    (latitudeFrameAt_orthogonal u hu) hq] with w hw
  have hsym : overlap u w = q := by
    calc
      overlap u w = overlap w u := by
        unfold overlap
        rw [real_inner_comm]
      _ = q := hw.2
  simp only [originalPureEffectivePotential, hsym]

/-- Exact effective latitude density, including the entropy power N-3. -/
theorem originalPureEffectivePotential_latitude_density
    (n p : ℕ) (hn : 1 ≤ n) (alpha β H : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (q : ℝ) (hq : |q| ≤ 1) :
    latitudeDensityPartition n 1
      (originalPureEffectivePotential n p alpha β H u) u q =
      (Real.sqrt (1-q^2))^(n-2) *
        Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*
          sourcePureLatitudeVariance p alpha q/2) := by
  unfold latitudeDensityPartition partitionAgainst
  congr 1
  have heq : (fun w => Real.exp (1*originalPureEffectivePotential n p alpha β H u w))
      =ᵐ[latitudeLaw u (latitudeFrameAt u) q]
      (fun _ => Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*
        sourcePureLatitudeVariance p alpha q/2)) := by
    filter_upwards [originalPureEffectivePotential_latitude_ae n p hn
      alpha β H u hu q hq] with w hw
    rw [hw,one_mul]
  rw [integral_congr_ae heq, integral_const]
  simp only [probReal_univ, one_smul]

theorem originalPureEffectivePotential_latitude_density_integrableOn
    (n p : ℕ) (hn : 1 ≤ n) (alpha β H : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    {lo hi : ℝ} (hlo : -1 < lo) (hhi : hi < 1) :
    IntegrableOn (latitudeDensityPartition n 1
      (originalPureEffectivePotential n p alpha β H u) u) (Icc lo hi) volume := by
  let g := fun q : ℝ => (Real.sqrt (1-q^2))^(n-2) *
    Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*sourcePureLatitudeVariance p alpha q/2)
  have hc : Continuous g := by
    dsimp [g, sourcePureLatitudeVariance]
    fun_prop
  have hi : IntegrableOn g (Icc lo hi) volume :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  apply hi.congr_fun
  · intro q hq
    exact (originalPureEffectivePotential_latitude_density n p hn
      alpha β H u hu q (abs_le.mpr ⟨(hlo.trans_le hq.1).le,
        (hq.2.trans_lt hhi).le⟩)).symm
  · exact measurableSet_Icc

/-- Exact source `pc-band-mean` for every closed band strictly inside
(-1,1). It is a direct theorem about the original conditional law and
original pure field, not an assumed conditional partition formula. -/
theorem pure_original_conditioned_band_mean_coarea
    (n p : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H : ℝ) {center width : ℝ} (hwidth : 0 ≤ width)
    (hbelow : -1 < center-width) (habove : center+width < 1) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Icc (center-width) (center+width)))
      ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) =
      (latitudeNormalization n).toReal *
        ∫ q in Icc (center-width) (center+width),
          (Real.sqrt (1-q^2))^(n-2) *
            Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*
              sourcePureLatitudeVariance p alpha q/2) ∂volume := by
  dsimp only
  let V := originalPureEffectivePotential n p alpha β H u
  have hV : Continuous V :=
    originalPureEffectivePotential_continuous n p alpha β H u
  have hden := originalPureEffectivePotential_latitude_density_integrableOn
    n p (by omega) alpha β H u hu hbelow habove
  rw [pure_original_conditioned_band_mean_sphere n p hp alpha halpha
    hQ u hu β H (Icc (center-width) (center+width)) measurableSet_Icc]
  have hpart :
      (∫ w in overlapRegion u (Icc (center-width) (center+width)),
        originalPureMeanProfile n p alpha β H u w ∂sphereLaw (n+1)) =
      partitionOn 1 V (overlapRegion u (Icc (center-width) (center+width))) := by
    unfold partitionOn
    apply integral_congr_ae
    exact .of_forall fun w => by
      simpa only [V, one_mul] using
        originalPureMeanProfile_eq_exp_effective n p alpha β H u w
  rw [hpart, partitionOn_symmetric_band_eq_real_integral hn 1 hV
    u hu hwidth hbelow habove hden]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
  exact originalPureEffectivePotential_latitude_density n p (by omega)
    alpha β H u hu q (abs_le.mpr ⟨(hbelow.trans_le hq.1).le,
      (hq.2.trans_lt habove).le⟩)

end
end SlowEquilibration.SphericalPureOriginalConditionalBandCoarea
