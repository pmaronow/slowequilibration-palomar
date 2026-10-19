module

public import SphericalAging.AnnealedCutoffProcess
public import SphericalAging.CanonicalSphereProcess

public section

/-! The actual product-space annealed cutoff paths preserve the physical
sphere. Section identities give the true sphere property at a countable
past grid; actual product-space continuous paths extend it to every time.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedSphereProcess
open HardSphereDynamics AnnealedCutoffProcess
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {ρ : Measure (Parameter N p)} [IsProbabilityMeasure ρ]
set_option maxHeartbeats 1000000

/-- Sphere preservation is a conclusion for the actual annealed product
process, on one probability-one event simultaneously through its horizon. -/
theorem process_onSphere (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ)
    (hinitial : ∀ᵐ q ∂ρ, OnSphere q.2) (T : ℝ≥0) :
    ∀ᵐ ω ∂ρ.prod P, ∀ t, t ≤ T →
      OnSphere (process (NullAugmentation.driver D) β R hR hJ T t ω) := by
  let D' := NullAugmentation.driver D
  let X := process D' β R hR hJ T
  have hfixed (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ ω ∂ρ.prod P, ‖X t ω‖^2=(N : ℝ) := by
    have hmeas : MeasurableSet {ω : Parameter N p × Ω | ‖X t ω‖^2=(N : ℝ)} :=
      ((((process_stronglyAdapted D' β R hR hJ T t).mono
        ((IndependentBackgroundDriver.filtration (Parameter N p) (NullAugmentation.augment F P)).le t)).norm).pow 2).measurableSet_eq_fun
          stronglyMeasurable_const
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [process_slice_global D' β R hR hJ T,hinitial] with q hq hi
    filter_upwards [hq,CanonicalSphereProcess.globalProcess_onSphere hN D β R hR hNR q hi]
      with ω heq hsphere
    change ‖process D' β R hR hJ T t (q,ω)‖^2=(N : ℝ)
    rw [heq t ht]
    exact (onSphere_iff_norm_sq _).mp (hsphere t)
  have hgrid : ∀ᵐ ω ∂ρ.prod P, ∀ n k : ℕ,
      ‖X (min (AdaptedContinuous.gridTime n k) T) ω‖^2=(N : ℝ) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => hfixed _ (min_le_right _ _)))
  filter_upwards [hgrid,process_continuous D' β R hR hJ T] with ω hg hc
  intro t ht
  apply (onSphere_iff_norm_sq _).mpr
  have hlim := ((hc.norm.pow 2).tendsto t).comp (AdaptedContinuous.tendsto_pastGrid t)
  have heq : (fun n => ‖X (AdaptedContinuous.pastGrid t n) ω‖^2) =
      (fun _ : ℕ => (N : ℝ)) := by
    funext n
    have hh := hg n ⌊t*(n+1)⌋₊
    change ‖X (min (AdaptedContinuous.pastGrid t n) T) ω‖^2=(N : ℝ) at hh
    simpa only [min_eq_left ((AdaptedContinuous.pastGrid_le t n).trans ht)] using hh
  change Tendsto (fun n => ‖X (AdaptedContinuous.pastGrid t n) ω‖^2) atTop (𝓝 (‖X t ω‖^2)) at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end SphericalAging.AnnealedSphereProcess
