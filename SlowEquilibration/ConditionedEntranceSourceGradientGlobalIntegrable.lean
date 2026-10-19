-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisFibreIntegrableTilt
public import SlowEquilibration.ConditionedEntranceJointGradientUniform
public import SlowEquilibration.ConditionedEntranceJointEnergyIntegralSum

/-! The actual physical weighted-gradient density is L¹ under the
single global source tilt, for the jointly measurable completed-graph
representatives supplied by the source energy theorem. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_joint_weighted_gradient_globalTilt_integrable
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (J : Disorder N μ.maxDegree) (hJ : J ∈ regularDisorder)
    (e k hbar kbar B R : ℝ)
    (hh : |e| ≤ hbar) (hk : |k| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s, |χ s| ≤ B) (hχR : ∀ s, R < |s| → χ s = 0)
    (F : SourceParameters N μ × Vector N → ℝ)
    (G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ)
    (hFsm : StronglyMeasurable F) (hGsm : ∀ ij, StronglyMeasurable (G ij))
    (hphys : ∀ v : Vector N, ∀ hv : OnSphere v,
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hv
      ∃ F₁ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
        (fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
        (fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst ∧
        (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
          1 ≤ F₁.val.fst x ∧
          ‖F₁.val.fst x‖ ≤
            1 + Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))) ∧
        sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u =
          rateLaplace D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous
            (PhysicalHitting.capKilling_nonneg α v) θ
            (killingVector D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
        ∀ ij : Fin N × Fin N,
          (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij)
    (M : ℝ) (hM : 0 < M) :
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun v x =>
      sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β * (H z.1 z.2-H₀ z.2)
    let f : Vector N × Vector N → ℝ := fun z =>
      F ((J,(z.1,(e,k))),z.2) *
        (∑ ij : Fin N × Fin N, (G ij ((J,(z.1,(e,k))),z.2))^2)
    Integrable f (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) := by
  dsimp only
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun v x =>
    sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
  let f : Vector N × Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,k))),z.2) *
      (∑ ij : Fin N × Fin N, (G ij ((J,(z.1,(e,k))),z.2))^2)
  let C := 1 + Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))
  let W := β * PhysicalHitting.uniformCutoffEnergyConstant μ Q hbar kbar B R *
    (N : ℝ) * α ^ μ.minDegree
  let Hf := 2 * Real.log 2 + 4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)
  let L := |2*C+Real.exp (2*W)*(θ : ℝ)*Hf|+1
  have hL : 0 ≤ L := by positivity
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector N × Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) by fun_prop)
  have hpair : Measurable (fun z : Vector N × Vector N =>
      (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) := by fun_prop
  have hFm : StronglyMeasurable (fun z : Vector N × Vector N =>
      F ((J,(z.1,(e,k))),z.2)) := hFsm.comp_measurable hpair
  have hGm (ij : Fin N × Fin N) : StronglyMeasurable (fun z : Vector N × Vector N =>
      G ij ((J,(z.1,(e,k))),z.2)) := (hGsm ij).comp_measurable hpair
  have hfm : StronglyMeasurable f := hFm.mul
    (Finset.stronglyMeasurable_fun_sum _ (fun ij _ => (hGm ij).pow 2))
  apply axis_gibbs_uniform_fibre_integrable_globalTilt hN β H₀ hH₀ H hH f hfm L hL
    ?_ M hM
  intro v hv
  let p : SourceParameters N μ := (J,(v,(e,k)))
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hv
  obtain ⟨F₁,u,hFref,hFgraph,hFb,hu,hGgraph⟩ := hphys v hv
  let π := gibbsLaw N β D.hamiltonian
  have hHpx (x : Vector N) : H v x = D.hamiltonian x := rfl
  have hFF : (fun x => F (p,x)) =ᵐ[π] F₁.val.fst := hFgraph
  have hGg (ij : Fin N × Fin N) :
      (fun x => G ij (p,x)) =ᵐ[π] u.val.snd ij := hGgraph ij
  let CF : ℝ≥0 := ⟨C,by positivity⟩
  have hFi : Integrable (fun x => f (v,x)) π := by
    exact weighted_gradient_density_integrable_of_graph_representatives
      hN β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ CF
        (hFb.mono (fun _ hx => hx.2)) (fun x => F (p,x))
        (fun ij x => G ij (p,x)) hFF hGg
  have hF0 : ∀ᵐ x ∂π, 0 ≤ F (p,x) := by
    filter_upwards [hFF,hFb] with x hx hb
    rw [hx]
    linarith [hb.1]
  have hfn : ∀ᵐ x ∂π, 0 ≤ f (v,x) := by
    filter_upwards [hF0] with x hx
    exact mul_nonneg hx (Finset.sum_nonneg (fun ij _ => sq_nonneg _))
  have hFmeas : Measurable (fun x => F (p,x)) :=
    (hFsm.comp_measurable (by fun_prop)).measurable
  have hGmeas (ij : Fin N × Fin N) : Measurable (fun x => G ij (p,x)) :=
    ((hGsm ij).comp_measurable (by fun_prop)).measurable
  have hsum := weighted_gradient_density_integral_eq_sum π (fun x => F (p,x))
    (fun ij x => G ij (p,x)) hFmeas hGmeas hF0 hFi
  have hBval : (∫ x, f (v,x) ∂π) = jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian μ Q hQ hnp α χ) F G p := by
    convert hsum using 1
    rfl
  have hb := source_joint_weighted_gradient_uniform_bound hN μ hnp Q hQ hQ1
    α hα χ hχ β hβ θ hθ p hv hJ hbar kbar B R hh hk hB hR hχB hχR
    F G u hFref hu hGgraph
  have hbs : (∫ x, f (v,x) ∂π) ≤ 2*C+Real.exp (2*W)*(θ : ℝ)*Hf :=
    hBval.trans_le hb.2
  have hAbsEq : (∫ x, |f (v,x)| ∂π) = ∫ x, f (v,x) ∂π :=
    integral_congr_ae (hfn.mono (fun x hx => abs_of_nonneg hx))
  have hπeq : gibbsLaw N β (H v) = π := rfl
  constructor
  · rw [hπeq]
    exact hFi
  · rw [hπeq,hAbsEq]
    exact hbs.trans (by
      dsimp only [L]
      linarith [le_abs_self (2*C+Real.exp (2*W)*(θ : ℝ)*Hf)])

end SlowEquilibration.ConditionedEntrance
