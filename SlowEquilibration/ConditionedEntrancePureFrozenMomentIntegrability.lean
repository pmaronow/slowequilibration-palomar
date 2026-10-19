-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability
public import SlowEquilibration.ConditionedEntrancePureJointSignedReducedEnergy
public import SlowEquilibration.ConditionedEntrancePureAxisCapHit

/-! Both source defect-square densities are L¹ for the same frozen-axis
reference graph representative that enters the physical signed energy
inequality. No separate global representative is selected. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem pure_frozen_reference_defect_moments_integrable
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (e : ℝ)
    (F : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (GF : (Fin N × Fin N) → SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (hFrozenF : ∀ p q x, p.1=q.1 → F (p,x)=F (q,x))
    (hFrozenGF : ∀ ij p q x, p.1=q.1 → GF ij (p,x)=GF ij (q,x))
    (F₀ : sphericalSobolevGraph hN β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)
      (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous)
    (v₀ : Vector N)
    (hFrep : (fun x => F ((J,(v₀,(e,0))),x)) =ᵐ[
      gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)] F₀.val.fst)
    (hGFrep : ∀ ij, (fun x => GF ij ((J,(v₀,(e,0))),x)) =ᵐ[
      gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)] F₀.val.snd ij)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J),
      1 ≤ F₀.val.fst x)
    (M : ℝ) (hM : 0 < M) :
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let H : Vector N → Vector N → ℝ := fun v x =>
      pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β*(H z.1 z.2-H₀ z.2)
    let Fa : Vector N × Vector N → ℝ := fun z =>
      F ((J,(z.1,(e,0))),z.2)
    let GFa : (Fin N × Fin N) → Vector N × Vector N → ℝ := fun ij z =>
      GF ij ((J,(z.1,(e,0))),z.2)
    Integrable (fun z => (tiltDefect w z)^2*(Fa z-1))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) ∧
    Integrable (fun z => (tiltDefect w z)^2*
      (∑ ij : Fin N × Fin N, (GFa ij z)^2/Fa z))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) := by
  dsimp only
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let H : Vector N → Vector N → ℝ := fun v x =>
    pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
  let w : Vector N × Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let Fa : Vector N × Vector N → ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
  let GFa : (Fin N × Fin N) → Vector N × Vector N → ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,0))),z.2)
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (pure_axisJointHamiltonian_contDiff d hd c hc Q α χ hχ J e).continuous
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hFaFrozen (u v x : Vector N) : Fa (u,x)=Fa (v,x) :=
    hFrozenF (J,(u,(e,0))) (J,(v,(e,0))) x rfl
  have hGFaFrozen (ij : Fin N × Fin N) (u v x : Vector N) :
      GFa ij (u,x)=GFa ij (v,x) :=
    hFrozenGF ij (J,(u,(e,0))) (J,(v,(e,0))) x rfl
  let π := gibbsLaw N β H₀
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hFrepr : (fun x => Fa (0,x)) =ᵐ[π] F₀.val.fst := by
    filter_upwards [hFrep] with x hx
    rw [hFaFrozen 0 v₀ x]
    exact hx
  have hGFrepr (ij : Fin N × Fin N) :
      (fun x => GFa ij (0,x)) =ᵐ[π] F₀.val.snd ij := by
    filter_upwards [hGFrep ij] with x hx
    change GFa ij (0,x)=F₀.val.snd ij x
    rw [hGFaFrozen ij 0 v₀ x]
    exact hx
  have hFi : Integrable (fun x => Fa (0,x)) π :=
    ((Lp.memLp F₀.val.fst).integrable (by norm_num)).congr hFrepr.symm
  exact frozen_reference_defect_moments_integrable hN β H₀ hH₀ w hw hM
    Fa GFa hFaFrozen hGFaFrozen F₀ hFrepr hGFrepr hFlo hFi

end SlowEquilibration.ConditionedEntrance
