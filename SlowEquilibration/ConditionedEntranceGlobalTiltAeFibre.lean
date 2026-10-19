-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisFibreIntegrableTilt
public import SlowEquilibration.SphericalGibbsEquivalentMeasures

/-! A pointwise property holding on each physical Gibbs fibre over the
spherical axes also holds almost everywhere under the single global
axis–spin tilt. This is used for F≥1 and 0≤U≤1 in global Cauchy bounds. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem ae_globalTilt_of_gibbs_fibres
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2))
    (P : Vector N × Vector N → Prop)
    (hPm : MeasurableSet {z | P z})
    (hP : ∀ u : Vector N, OnSphere u →
      ∀ᵐ x ∂gibbsLaw N β (H u), P (u,x))
    (w : Vector N × Vector N → ℝ) (M : ℝ) :
    ∀ᵐ z ∂normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M,
      P z := by
  let : IsProbabilityMeasure (gibbsLaw N β H₀) := gibbsLaw_probability hN β hH₀
  have hHu (u : Vector N) : Continuous (H u) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hbase : ∀ᵐ z ∂(sphereLaw N).prod (gibbsLaw N β H₀), P z := by
    apply (Measure.ae_prod_iff_ae_ae hPm).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    have hus : OnSphere u := (onSphere_iff_norm_sq u).mpr hu
    have hAC : ae (gibbsLaw N β H₀) ≤ ae (gibbsLaw N β (H u)) :=
      (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β (H u) H₀ (hHu u)).ae_le
    exact (hP u hus).filter_mono hAC
  exact hbase.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

end SlowEquilibration.ConditionedEntrance
