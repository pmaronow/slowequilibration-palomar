-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeakResolvent
public import SlowEquilibration.SphericalGibbsOscillation
public import SphericalAging.LandscapeDerivatives

/-! Actual completed spherical Sobolev graphs transport between continuous
Gibbs laws by the literal identity on functions and rotation gradients.
Finite density bounds are used for continuity of transport only. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem gibbsToL2_changeMeasure (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (c : ℝ≥0∞) (hc : c≠⊤) (hcmp : gibbsLaw N β₁ H₁ ≤ c • gibbsLaw N β₀ H₀)
    (f : Vector N → ℝ) (hf : Continuous f) :
    Lp.LpToLpOfMeasureLeSMul hc hcmp (gibbsToL2 hN β₀ H₀ hH₀ f hf)=
      gibbsToL2 hN β₁ H₁ hH₁ f hf := by
  have ha := Measure.absolutelyContinuous_of_le_smul hcmp
  apply Lp.ext
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc hcmp (gibbsToL2 hN β₀ H₀ hH₀ f hf),
    ha.ae_eq (gibbsToL2_coe hN β₀ H₀ hH₀ f hf),gibbsToL2_coe hN β₁ H₁ hH₁ f hf]
      with x hT h₀ h₁
  exact (hT.trans h₀).trans h₁.symm

theorem normalizedRotationGradientL2_changeMeasure (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (c : ℝ≥0∞) (hc : c≠⊤) (hcmp : gibbsLaw N β₁ H₁ ≤ c • gibbsLaw N β₀ H₀)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) (ij : Fin N × Fin N) :
    Lp.LpToLpOfMeasureLeSMul hc hcmp (normalizedRotationGradientL2 hN β₀ H₀ hH₀ f hf ij)=
      normalizedRotationGradientL2 hN β₁ H₁ hH₁ f hf ij := by
  change Lp.LpToLpOfMeasureLeSMul hc hcmp (gradientScale N •
    gibbsToL2 hN β₀ H₀ hH₀ _ (lieDerivative_continuous _ hf))=
    gradientScale N • gibbsToL2 hN β₁ H₁ hH₁ _ (lieDerivative_continuous _ hf)
  rw [map_smul,gibbsToL2_changeMeasure]

/-- Literal graph transport is derived by transporting the actual smooth
approximants through the continuous identity map between the two L2 laws. -/
theorem sphericalSobolevGraph_changeMeasure (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (c : ℝ≥0∞) (hc : c≠⊤) (hcmp : gibbsLaw N β₁ H₁ ≤ c • gibbsLaw N β₀ H₀)
    (u : sphericalSobolevGraph hN β₀ H₀ hH₀) :
    ∃ v : sphericalSobolevGraph hN β₁ H₁ hH₁,
      v.val.fst=Lp.LpToLpOfMeasureLeSMul hc hcmp u.val.fst ∧
      ∀ ij : Fin N × Fin N,v.val.snd ij=Lp.LpToLpOfMeasureLeSMul hc hcmp (u.val.snd ij) := by
  let T : Lp ℝ 2 (gibbsLaw N β₀ H₀) →L[ℝ] Lp ℝ 2 (gibbsLaw N β₁ H₁) :=
    Lp.LpToLpOfMeasureLeSMul hc hcmp
  have hm : u.val∈closure (Set.range (smoothGradientGraphLinear hN β₀ H₀ hH₀)) := u.property
  obtain ⟨q,hq,hqLim⟩ := mem_closure_iff_seq_limit.mp hm
  choose f hf using hq
  have hseq : (fun n => smoothGradientGraphLinear hN β₀ H₀ hH₀ (f n))=q := funext hf
  rw [← hseq] at hqLim
  have hp := ((WithLp.homeomorphProd 2 _ _).continuous.tendsto u.val).comp hqLim
  have hU := (continuous_fst.tendsto u.val.ofLp).comp hp
  have hG := (continuous_snd.tendsto u.val.ofLp).comp hp
  change Tendsto (fun n => gibbsToL2 hN β₀ H₀ hH₀ (f n) (smoothCore_contDiff (f n)).continuous)
    atTop (𝓝 u.val.fst) at hU
  change Tendsto (fun n => normalizedRotationGradientL2 hN β₀ H₀ hH₀ (f n)
    ((smoothCore_contDiff (f n)).of_le (by simp))) atTop (𝓝 u.val.snd) at hG
  have hV : Tendsto (fun n => gibbsToL2 hN β₁ H₁ hH₁ (f n) (smoothCore_contDiff (f n)).continuous)
      atTop (𝓝 (T u.val.fst)) := by
    have ht := T.continuous.continuousAt.tendsto.comp hU
    exact ht.congr' (.of_forall (fun n => gibbsToL2_changeMeasure hN β₀ β₁ H₀ H₁ hH₀ hH₁ c hc hcmp _ _))
  let G := WithLp.toLp 2 (fun ij : Fin N × Fin N => T (u.val.snd ij))
  have hDG : Tendsto (fun n => normalizedRotationGradientL2 hN β₁ H₁ hH₁ (f n)
      ((smoothCore_contDiff (f n)).of_le (by simp))) atTop (𝓝 G) := by
    apply (PiLp.continuous_toLp (p:=2) (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β₁ H₁))).continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro ij
    have ht := T.continuous.continuousAt.tendsto.comp
      ((PiLp.continuous_apply 2 _ ij).continuousAt.tendsto.comp hG)
    exact ht.congr' (.of_forall (fun n => normalizedRotationGradientL2_changeMeasure hN β₀ β₁ H₀ H₁ hH₀ hH₁ c hc hcmp _ _ ij))
  let z := WithLp.toLp 2 (T u.val.fst,G)
  have hz : z∈closure (Set.range (smoothGradientGraphLinear hN β₁ H₁ hH₁)) := by
    apply mem_closure_of_tendsto
      ((WithLp.homeomorphProd 2 _ _).symm.continuous.continuousAt.tendsto.comp (hV.prodMk_nhds hDG))
    exact .of_forall (fun n => ⟨f n,rfl⟩)
  exact ⟨⟨z,hz⟩,rfl,fun _ => rfl⟩

/-- Any two continuous spherical Gibbs Hamiltonians have the same actual
completed Sobolev functions and gradients, under the literal identity.
No cross-Gibbs form-domain compatibility is supplied as a premise. -/
theorem sphericalSobolevGraph_changeGibbs (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (u : sphericalSobolevGraph hN β₀ H₀ hH₀) :
    ∃ v : sphericalSobolevGraph hN β₁ H₁ hH₁,
      (v.val.fst=ᵐ[gibbsLaw N β₁ H₁] u.val.fst) ∧
      ∀ ij : Fin N × Fin N,v.val.snd ij=ᵐ[gibbsLaw N β₁ H₁] u.val.snd ij := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).exists_bound_of_continuousOn
    ((hH₁.const_mul β₁).sub (hH₀.const_mul β₀)).continuousOn
  have hl : ∀ x,OnSphere x → -B ≤ β₁*H₁ x-β₀*H₀ x := by
    intro x hx
    have hball : x∈Metric.closedBall (0 : Vector N) (Real.sqrt N) := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)).le
    have hb := hB x hball
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).1
  have hh : ∀ x,OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ B := by
    intro x hx
    have hball : x∈Metric.closedBall (0 : Vector N) (Real.sqrt N) := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)).le
    have hb := hB x hball
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).2
  have hcmp := gibbsLaw_le_of_sphere_energy_bounds hN β₀ β₁ hH₀ hH₁ hl hh
  obtain ⟨v,hv,hG⟩ := sphericalSobolevGraph_changeMeasure hN β₀ β₁ H₀ H₁ hH₀ hH₁
    (ENNReal.ofReal (Real.exp (B-(-B)))) ENNReal.ofReal_ne_top hcmp u
  refine ⟨v,?_,?_⟩
  · rw [hv]
    exact Lp.coeFn_LpToLpOfMeasureLeSMul _ hcmp _
  · intro ij
    rw [hG ij]
    exact Lp.coeFn_LpToLpOfMeasureLeSMul _ hcmp _

end SlowEquilibration.SphericalForm
