-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability
public import SlowEquilibration.ConditionedEntranceJointSignedReducedEnergy

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

theorem source_frozen_reference_defect_moments_integrable
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (β : ℝ) (J : Disorder N μ.maxDegree) (e k : ℝ)
    (F : SourceParameters N μ × Vector N → ℝ)
    (GF : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ)
    (hFrozenF : ∀ p q x, p.1=q.1 → F (p,x)=F (q,x))
    (hFrozenGF : ∀ ij p q x, p.1=q.1 → GF ij (p,x)=GF ij (q,x))
    (F₀ : sphericalSobolevGraph hN β (fieldOfMixture μ J)
      (fieldOfMixture_contDiff μ J).continuous)
    (v₀ : Vector N)
    (hFrep : (fun x => F ((J,(v₀,(e,k))),x)) =ᵐ[
      gibbsLaw N β (fieldOfMixture μ J)] F₀.val.fst)
    (hGFrep : ∀ ij, (fun x => GF ij ((J,(v₀,(e,k))),x)) =ᵐ[
      gibbsLaw N β (fieldOfMixture μ J)] F₀.val.snd ij)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β (fieldOfMixture μ J),
      1 ≤ F₀.val.fst x)
    (M : ℝ) (hM : 0 < M) :
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun v x =>
      sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β*(H z.1 z.2-H₀ z.2)
    let Fa : Vector N × Vector N → ℝ := fun z =>
      F ((J,(z.1,(e,k))),z.2)
    let GFa : (Fin N × Fin N) → Vector N × Vector N → ℝ := fun ij z =>
      GF ij ((J,(z.1,(e,k))),z.2)
    Integrable (fun z => (tiltDefect w z)^2*(Fa z-1))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) ∧
    Integrable (fun z => (tiltDefect w z)^2*
      (∑ ij : Fin N × Fin N, (GFa ij z)^2/Fa z))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) := by
  dsimp only
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun v x =>
    sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
  let w : Vector N × Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let Fa : Vector N × Vector N → ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
  let GFa : (Fin N × Fin N) → Vector N × Vector N → ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,k))),z.2)
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ).comp
      (show Continuous (fun z : Vector N × Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hFaFrozen (u v x : Vector N) : Fa (u,x)=Fa (v,x) :=
    hFrozenF (J,(u,(e,k))) (J,(v,(e,k))) x rfl
  have hGFaFrozen (ij : Fin N × Fin N) (u v x : Vector N) :
      GFa ij (u,x)=GFa ij (v,x) :=
    hFrozenGF ij (J,(u,(e,k))) (J,(v,(e,k))) x rfl
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
