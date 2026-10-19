-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisMeasurableDisintegration
public import SlowEquilibration.ConditionedEntranceNormalizedTiltIntegrable
public import SlowEquilibration.SphericalBaseGibbsPartitionFamily

/-! Uniform absolute Gibbs-fibre bounds imply actual L¹ under the
single globally normalized axis–spin tilt. The physical fibre partition
ratio is retained throughout the product-measure calculation. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem axis_gibbs_uniform_fibre_integrable_globalTilt
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2))
    (f : Vector N × Vector N → ℝ) (hf : StronglyMeasurable f)
    (L : ℝ) (_hL : 0 ≤ L)
    (hFibre : ∀ u : Vector N, OnSphere u →
      Integrable (fun x => f (u,x)) (gibbsLaw N β (H u)) ∧
      (∫ x, |f (u,x)| ∂gibbsLaw N β (H u)) ≤ L)
    (M : ℝ) (hM : 0 < M) :
    let w : Vector N × Vector N → ℝ := fun z =>
      β * (H z.1 z.2 - H₀ z.2)
    Integrable f (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) := by
  dsimp only
  let θ := sphereLaw N
  let π := gibbsLaw N β H₀
  let w : Vector N × Vector N → ℝ := fun z => β * (H z.1 z.2-H₀ z.2)
  let m : Vector N → ℝ := fun u => partition N β (H u) / partition N β H₀
  let g : Vector N × Vector N → ℝ := fun z => Real.exp (w z)*f z
  let : IsProbabilityMeasure θ := sphereLaw_probability N
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hHu (u : Vector N) : Continuous (H u) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hmpos (u : Vector N) : 0 < m u :=
    div_pos (partition_pos hN β (hHu u)) (partition_pos hN β hH₀)
  have hmc : Continuous m :=
    (jointHamiltonianPartition_continuous hN β
      (fun z : Vector N × Vector N => H z.1 z.2) hH).div_const _
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).exists_bound_of_continuousOn
    hmc.continuousOn
  have hC0 : 0 ≤ C := by
    have hzero : (0 : Vector N) ∈ closedBall 0 (Real.sqrt N) := by
      simp only [mem_closedBall,dist_self]
      exact Real.sqrt_nonneg _
    exact (norm_nonneg _).trans (hC 0 hzero)
  have hmC (u : Vector N) (hu : OnSphere u) : m u ≤ C := by
    have hus : ‖u‖^2=(N : ℝ) := (onSphere_iff_norm_sq u).mp hu
    have hball : u ∈ closedBall 0 (Real.sqrt N) := by
      simp only [mem_closedBall,dist_zero_right]
      rw [← hus,Real.sqrt_sq (norm_nonneg u)]
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC u hball)
  have hsource (u : Vector N) :
      gibbsLaw N β (H u) = normalizedTilt π (fun x => w (u,x)) (m u) := by
    calc
      gibbsLaw N β (H u) = normalizedTilt π
          (gibbsEnergyDifference β β H₀ (H u)) (m u) :=
        gibbsLaw_normalizedTilt hN β β H₀ (H u) hH₀ (hHu u)
      _ = normalizedTilt π (fun x => w (u,x)) (m u) := by
        congr 1
        funext x
        dsimp only [w,gibbsEnergyDifference]
        ring
  have htw (u : Vector N) : Measurable (fun x => w (u,x)) :=
    (hw.comp (continuous_const.prodMk continuous_id)).measurable
  have hgm : StronglyMeasurable g := hw.rexp.stronglyMeasurable.mul hf
  have hgi : ∀ᵐ u ∂θ, Integrable (fun x => g (u,x)) π := by
    filter_upwards [sphereLaw_support hN] with u hu
    have hus : OnSphere u := (onSphere_iff_norm_sq u).mpr hu
    have hi := (hFibre u hus).1
    rw [hsource u] at hi
    exact (integrable_normalizedTilt_iff π (fun x => w (u,x))
      (fun x => f (u,x)) (htw u) (hmpos u)).1 hi
  have hnormeq (u : Vector N) :
      (fun x => ‖g (u,x)‖) = fun x => Real.exp (w (u,x))*|f (u,x)| := by
    funext x
    dsimp only [g]
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.norm_eq_abs]
  have hnormfibre (u : Vector N) :
      (∫ x, ‖g (u,x)‖ ∂π) =
      m u * (∫ x, |f (u,x)| ∂gibbsLaw N β (H u)) := by
    rw [hnormeq, hsource u, integral_normalizedTilt π _ (htw u) (hmpos u)]
    field_simp [(hmpos u).ne']
  have houterm : Measurable (fun u => ∫ x, ‖g (u,x)‖ ∂π) :=
    hgm.norm.integral_prod_right'.measurable
  have houter : Integrable (fun u => ∫ x, ‖g (u,x)‖ ∂π) θ := by
    apply Integrable.of_bound houterm.aestronglyMeasurable (C*L)
    filter_upwards [sphereLaw_support hN] with u hu
    have hus : OnSphere u := (onSphere_iff_norm_sq u).mpr hu
    have hfi := (hFibre u hus).1
    have hfnon : 0 ≤ ∫ x, |f (u,x)| ∂gibbsLaw N β (H u) :=
      integral_nonneg (fun _ => abs_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),hnormfibre]
    exact mul_le_mul (hmC u hus) (hFibre u hus).2 hfnon hC0
  have hprod : Integrable g (θ.prod π) :=
    (integrable_prod_iff hgm.aestronglyMeasurable).2 ⟨hgi,houter⟩
  exact (integrable_normalizedTilt_iff (θ.prod π) w f hw.measurable hM).2 hprod

end SlowEquilibration.ConditionedEntrance
