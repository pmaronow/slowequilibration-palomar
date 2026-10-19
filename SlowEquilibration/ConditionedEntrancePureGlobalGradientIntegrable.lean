-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureKilledFiniteEnergy
public import SlowEquilibration.ConditionedEntrancePureJointSignedReducedEnergy
public import SlowEquilibration.ConditionedEntranceAxisFibreIntegrableTilt
public import SlowEquilibration.ConditionedEntranceJointEnergyIntegralSum

/-! Integrability of the proper-pure physical weighted gradient under the
single global tilt. Compactness is used only for finite integrability;
no exponentially large compact bound enters the eventual entrance rate. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral
open SphericalAging HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 1100000

theorem pure_joint_weighted_gradient_globalTilt_integrable
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (e : ℝ)
    (F : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (G : (Fin N × Fin N) →
      SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (hFsm : StronglyMeasurable F) (hGsm : ∀ ij, StronglyMeasurable (G ij))
    (hphys : ∀ v : Vector N, OnSphere v →
      let D := FieldData.ofPure hN d hd c hc Q J v e α χ hχ
      let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) J
      ∃ F₁ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
        (fun x => F ((J,(v,(e,0))),x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          referenceRate D₀ β θ (referenceInitialVector D₀ β) ∧
        (fun x => F ((J,(v,(e,0))),x)) =ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst ∧
        (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
          1 ≤ F₁.val.fst x ∧ ‖F₁.val.fst x‖ ≤
            1+Real.exp (2*β*derivativeConstant
              (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ))) ∧
        sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u =
          rateLaplace D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous
            (PhysicalHitting.capKilling_nonneg α v) θ
            (killingVector D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
        ∀ ij : Fin N × Fin N,
          (fun x => G ij ((J,(v,(e,0))),x)) =ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij)
    (M : ℝ) (hM : 0 < M) :
    let μ := FiniteMixture.pure d hd c hc
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun v x =>
      pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
    let w : Vector N × Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
    Integrable (fun z : Vector N × Vector N =>
      F ((J,(z.1,(e,0))),z.2)*
        (∑ ij : Fin N × Fin N, (G ij ((J,(z.1,(e,0))),z.2))^2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M) := by
  dsimp only
  let μ := FiniteMixture.pure d hd c hc
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun v x =>
    pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
  let w : Vector N × Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let f : Vector N × Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,0))),z.2)*
      (∑ ij : Fin N × Fin N, (G ij ((J,(z.1,(e,0))),z.2))^2)
  let B := derivativeConstant (mixtureCoefficients μ)*(N : ℝ)
  let C := 1+Real.exp (2*β*B)
  let Hf := 2*Real.log 2+4*β*B
  have hB : 0 ≤ B := mul_nonneg (derivativeConstant_pos _).le (Nat.cast_nonneg N)
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (pureSourceJointHamiltonian_contDiff d hd c hc Q α χ hχ).continuous.comp
      (show Continuous (fun z : Vector N × Vector N =>
        ((J,(z.1,(e,(0 : ℝ)))),z.2)) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  obtain ⟨W,hW⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      hw.continuousOn
  let L := |2*C+Real.exp (2*W)*(θ : ℝ)*Hf|+1
  have hL : 0 ≤ L := by positivity
  have hpair : Measurable (fun z : Vector N × Vector N =>
      (((J,(z.1,(e,0))),z.2) : SourceParameters N μ × Vector N)) := by fun_prop
  have hFm := hFsm.comp_measurable hpair
  have hGm (ij : Fin N × Fin N) := (hGsm ij).comp_measurable hpair
  have hfm : StronglyMeasurable f := hFm.mul
    (Finset.stronglyMeasurable_fun_sum _ (fun ij _ => (hGm ij).pow 2))
  apply axis_gibbs_uniform_fibre_integrable_globalTilt hN β H₀ hH₀ H hH f hfm L hL
    ?_ M hM
  intro v hv
  let D := FieldData.ofPure hN d hd c hc Q J v e α χ hχ
  let D₀ := FieldData.ofOriginal hN μ J
  let π := gibbsLaw N β D.hamiltonian
  have hHfun : H v = D.hamiltonian := (FieldData.ofPure_hamiltonian
    hN d hd c hc Q J v e α χ hχ).symm
  have hWv : ∀ x, OnSphere x → |β*D.hamiltonian x-β*D₀.hamiltonian x| ≤ W := by
    intro x hx
    have hvn := LandscapeDerivatives.sphere_norm v ((onSphere_iff_norm_sq v).mp hv)
    have hxn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
    have hb := hW (v,x) ⟨by simp only [mem_closedBall,dist_zero_right,hvn,le_refl],
      by simp only [mem_closedBall,dist_zero_right,hxn,le_refl]⟩
    change ‖w (v,x)‖ ≤ W at hb
    rw [Real.norm_eq_abs] at hb
    simpa only [w,H₀,D₀,FieldData.ofOriginal_hamiltonian,← hHfun,mul_sub] using hb
  obtain ⟨F₁,u,hFref,hFgraph,hFb,hu,hGgraph⟩ := hphys v hv
  let CF : ℝ≥0 := ⟨C,by positivity⟩
  have hFbound : ∀ᵐ x ∂π, ‖F₁.val.fst x‖ ≤ CF := by
    change ∀ᵐ x ∂gibbsLaw N β D.hamiltonian, ‖F₁.val.fst x‖ ≤ C
    simpa only [C,B,μ,mul_assoc] using hFb.mono (fun _ hx => hx.2)
  have hFi : Integrable (fun x => f (v,x)) π :=
    weighted_gradient_density_integrable_of_graph_representatives hN β
      D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ CF hFbound
      (fun x => F ((J,(v,(e,0))),x)) (fun ij x => G ij ((J,(v,(e,0))),x))
      hFgraph hGgraph
  have hF0 : ∀ᵐ x ∂π, 0 ≤ F ((J,(v,(e,0))),x) := by
    filter_upwards [hFgraph,hFb] with x hx hb
    rw [hx]
    linarith [hb.1]
  have hfn : ∀ᵐ x ∂π, 0 ≤ f (v,x) :=
    hF0.mono (fun x hx => mul_nonneg hx (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  obtain ⟨_,F₁',u',_,hF₁',_,hu',_,_,hBu⟩ := field_reference_finite_gradient_energy
    D D₀ β hβ θ hθ B hB (original_regular_hamiltonian_bound hN μ J hJ) W hWv
    (PhysicalHitting.capKilling α v) (PhysicalHitting.capKilling_contDiff α v).continuous
    (PhysicalHitting.capKilling_nonneg α v) (PhysicalHitting.capKilling_le_one hα v)
  have heu : u'=u := sphericalEnergyL2Map_injective hN β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) (hu'.trans hu.symm)
  have heF : F₁'=F₁ := sphericalSobolevGraph_eq_of_value_ae hN β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) F₁' F₁ (hF₁'.trans (hFref.symm.trans hFgraph))
  rw [heu,heF] at hBu
  have hFm' : Measurable (fun x => F ((J,(v,(e,0))),x)) :=
    (hFsm.comp_measurable (by fun_prop)).measurable
  have hGm' (ij : Fin N × Fin N) : Measurable (fun x => G ij ((J,(v,(e,0))),x)) :=
    ((hGsm ij).comp_measurable (by fun_prop)).measurable
  have hsum := weighted_gradient_density_integral_eq_sum π
    (fun x => F ((J,(v,(e,0))),x)) (fun ij x => G ij ((J,(v,(e,0))),x))
    hFm' hGm' hF0 hFi
  have hEq : (∫ x, f (v,x) ∂π) = sphericalWeightedGradientSquare hN β
      D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ := by
    rw [hsum]
    unfold sphericalWeightedGradientSquare
    apply Finset.sum_congr rfl
    intro ij _
    apply integral_congr_ae
    filter_upwards [hFgraph,hGgraph ij] with x hf hg
    rw [hf,hg]
  have hAbsEq : (∫ x, |f (v,x)| ∂π) = ∫ x, f (v,x) ∂π :=
    integral_congr_ae (hfn.mono (fun _ hx => abs_of_nonneg hx))
  rw [hHfun]
  refine ⟨hFi,?_⟩
  rw [hAbsEq,hEq]
  apply hBu.trans
  change 2*C+Real.exp (2*W)*(θ : ℝ)*Hf ≤ L
  exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)

end SlowEquilibration.ConditionedEntrance
