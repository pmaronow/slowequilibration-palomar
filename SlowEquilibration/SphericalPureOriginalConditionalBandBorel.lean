-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureOriginalConditionalBandCoarea
public import SlowEquilibration.SphericalTAPLatitudeBorelCoarea

@[expose] public section

/-! Full Borel-set version of manuscript equation `pc-band-mean` for the
original pure Hamiltonian under its genuine critical-value posterior. -/

namespace SlowEquilibration.SphericalPureOriginalConditionalBandBorel
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalPureOriginalConditionalBandFubini
open SphericalPureOriginalConditionalBandCoarea
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPLatitudeBorelCoarea
set_option autoImplicit false

/-- Exact source band mean for every Borel latitude set inside (-1,1).
The displayed entropy weight is `(1-q²)^((N-3)/2)` in square-root power
notation, with `N=n+1`, and the prefactor is the genuine sphere coarea
normalization. -/
theorem pure_original_conditioned_band_mean_borel
    (n p : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H : ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (hinside : I ⊆ Ioo (-1:ℝ) 1) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I)
      ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) =
      (latitudeNormalization n).toReal *
        ∫ q in I, (Real.sqrt (1-q^2))^(n-2) *
          Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*
            sourcePureLatitudeVariance p alpha q/2) ∂volume := by
  dsimp only
  let V := originalPureEffectivePotential n p alpha β H u
  have hV : Continuous V :=
    originalPureEffectivePotential_continuous n p alpha β H u
  let g := fun q : ℝ => (Real.sqrt (1-q^2))^(n-2) *
    Real.exp (β*H*q^p+(n+1 : ℕ)*β^2*sourcePureLatitudeVariance p alpha q/2)
  have hg : Continuous g := by
    dsimp [g, sourcePureLatitudeVariance]
    fun_prop
  have hsub : I ⊆ Icc (-1:ℝ) 1 := fun q hq =>
    ⟨(hinside hq).1.le,(hinside hq).2.le⟩
  have hgi : IntegrableOn g I volume :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hden : IntegrableOn (latitudeDensityPartition n 1 V u) I volume := by
    apply hgi.congr_fun
    · intro q hq
      exact (originalPureEffectivePotential_latitude_density n p (by omega)
        alpha β H u hu q (abs_le.mpr ⟨(hinside hq).1.le,
          (hinside hq).2.le⟩)).symm
    · exact hI
  rw [pure_original_conditioned_band_mean_sphere n p hp alpha halpha
    hQ u hu β H I hI]
  have hpart :
      (∫ w in overlapRegion u I,
        originalPureMeanProfile n p alpha β H u w ∂sphereLaw (n+1)) =
      partitionOn 1 V (overlapRegion u I) := by
    unfold partitionOn
    apply integral_congr_ae
    exact .of_forall fun w => by
      simpa only [V, one_mul] using
        originalPureMeanProfile_eq_exp_effective n p alpha β H u w
  rw [hpart, partitionOn_borel_latitude_eq_real_integral hn 1 hV
    u hu I hI hsub hden]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hI] with q hq
  exact originalPureEffectivePotential_latitude_density n p (by omega)
    alpha β H u hu q (abs_le.mpr ⟨(hinside hq).1.le,
      (hinside hq).2.le⟩)

end
end SlowEquilibration.SphericalPureOriginalConditionalBandBorel
