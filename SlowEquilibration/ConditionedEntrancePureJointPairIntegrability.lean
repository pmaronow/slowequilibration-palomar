-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourcePairIntegrable
public import SlowEquilibration.ConditionedEntrancePureGlobalBounds
public import SlowEquilibration.ConditionedEntrancePureReferenceBounds
public import SlowEquilibration.ConditionedEntranceAxisSourcePairGlobal

/-! The four exact source-pairing terms are L¹ for the physical source
joint representatives on the original regular-disorder bank. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 750000

private theorem pure_pair_continuous_integrable_of_ac {N : ℕ} (hN : 1≤N)
    (β : ℝ) (H₀ : Vector N→ℝ) (hH₀ : Continuous H₀)
    (ν : Measure (Vector N×Vector N)) [IsFiniteMeasure ν]
    (hν : ν ≪ (sphereLaw N).prod (gibbsLaw N β H₀))
    {f : Vector N×Vector N→ℝ} (hf : Continuous f) : Integrable f ν := by
  let : IsProbabilityMeasure (gibbsLaw N β H₀) := gibbsLaw_probability hN β hH₀
  have hs : ∀ᵐ z : Vector N×Vector N
      ∂(sphereLaw N).prod (gibbsLaw N β H₀),
      ‖z.1‖^2=(N : ℝ) ∧ ‖z.2‖^2=(N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with v hv
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact ⟨hv,hx⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs.filter_mono hν.ae_le] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

theorem pure_joint_positive_pair_four_integrable
    {N : ℕ} (hN : 1≤N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (hJ : J∈regularDisorder)
    (e M : ℝ) (hM : 0<M)
    (hMphys : M=∫ z : Vector N×Vector N,
      Real.exp (β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
        fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J))))
    (F U : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ)
    (GF G : (Fin N×Fin N)→SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (hGF : ∀ ij, StronglyMeasurable (GF ij))
    (hG : ∀ ij, StronglyMeasurable (G ij))
    (hphys : ∀ v : Vector N, OnSphere v →
      ∀ᵐ x ∂gibbsLaw N β
        (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
        1≤F ((J,(v,(e,0))),x) ∧
        ‖F ((J,(v,(e,0))),x)‖≤
          1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) ∧
        0≤U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x)≤1)
    (hRi : Integrable (fun z : Vector N×Vector N =>
      PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,0))),z.2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hKi : Integrable (fun z : Vector N×Vector N =>
      (tiltDefect (fun y : Vector N×Vector N =>
        β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J y.2)) z)^2*
        (∑ ij : Fin N×Fin N,
          (GF ij ((J,(z.1,(e,0))),z.2))^2/F ((J,(z.1,(e,0))),z.2)))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hBi : Integrable (fun z : Vector N×Vector N =>
      F ((J,(z.1,(e,0))),z.2)*
        (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,0))),z.2))^2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M)) :
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let w : Vector N×Vector N→ℝ := fun z =>
      β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
    let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
    let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
      GF ij ((J,(z.1,(e,0))),z.2)
    let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
      G ij ((J,(z.1,(e,0))),z.2)
    let I : Vector N×Vector N→ℝ := fun z =>
      1+uniformInitialDensity N β H₀ z.2
    Integrable (fun z => I z*Ua z) ν ∧
    Integrable (fun z => PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z)) ν ∧
    Integrable (fun z => tiltDefect w z*(I z-Fa z)*Ua z) ν ∧
    Integrable (fun z => tiltDefect w z*
      (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z)) ν := by
  dsimp only
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let H : Vector N→Vector N→ℝ := fun v x =>
    pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
  let w : Vector N×Vector N→ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let π := gibbsLaw N β H₀
  let ν₀ := (sphereLaw N).prod π
  let ν := normalizedTilt ν₀ w M
  let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
  let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
  let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,0))),z.2)
  let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    G ij ((J,(z.1,(e,0))),z.2)
  let I : Vector N×Vector N→ℝ := fun z =>
    1+uniformInitialDensity N β H₀ z.2
  let C := 1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ))
  have hC : 0≤C := by positivity
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2) := by
    have hMap : Continuous (fun z : Vector N×Vector N =>
        ((J,(z.1,(e,(0 : ℝ)))),z.2)) := by fun_prop
    exact (pureSourceJointHamiltonian_contDiff d hd c hc Q α χ hχ).continuous.comp hMap
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have heExp : Integrable (fun z => Real.exp (w z)) ν₀ :=
    pure_pair_continuous_integrable_of_ac hN β H₀ hH₀ ν₀ (by rfl) hw.rexp
  let : IsProbabilityMeasure ν := normalizedTilt_probability ν₀ w hM heExp hMphys.symm
  have hν : ν ≪ ν₀ := withDensity_absolutelyContinuous _ _
  have hpair : Measurable (fun z : Vector N×Vector N =>
      (((J,(z.1,(e,0))),z.2) : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N)) := by fun_prop
  have hFm : Measurable Fa := (hF.comp_measurable hpair).measurable
  have hUm : Measurable Ua := (hU.comp_measurable hpair).measurable
  have hGFm : ∀ ij, Measurable (GFa ij) := fun ij =>
    ((hGF ij).comp_measurable hpair).measurable
  have hGm : ∀ ij, Measurable (Ga ij) := fun ij =>
    ((hG ij).comp_measurable hpair).measurable
  have hIc : Continuous I := continuous_const.add
    ((uniformInitialDensity_continuous β H₀ hH₀).comp continuous_snd)
  have hk : Continuous (tiltDefect w) := by unfold tiltDefect; fun_prop
  have hIi : Integrable I ν :=
    pure_pair_continuous_integrable_of_ac hN β H₀ hH₀ ν hν hIc
  have hki : Integrable (tiltDefect w) ν :=
    pure_pair_continuous_integrable_of_ac hN β H₀ hH₀ ν hν hk
  have hH₀bound (x : Vector N) (hx : OnSphere x) :
      |H₀ x|≤derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ) := by
    have hn := SphericalAging.LandscapeDerivatives.sphere_norm x
      ((onSphere_iff_norm_sq x).mp hx)
    exact (field_regularDisorder_ball_bounds hN (mixtureCoefficients (FiniteMixture.pure d hd c hc))
      J hJ x (by rw [hn])).1
  have hIb₀ : ∀ᵐ z ∂ν₀,‖I z‖≤C := by
    apply (Measure.ae_prod_iff_ae_ae (by
      change MeasurableSet {z | ‖I z‖≤C}
      exact measurableSet_le hIc.norm.measurable measurable_const)).mpr
    filter_upwards [] with v
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    have hb := uniformInitialDensity_le hN β hβ H₀ hH₀
      (derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ))
      hH₀bound x ((onSphere_iff_norm_sq x).mpr hx)
    change ‖1+uniformInitialDensity N β H₀ x‖≤C
    rw [Real.norm_eq_abs,abs_of_nonneg (by
      have hp := uniformInitialDensity_pos hN β H₀ hH₀ x
      linarith)]
    simpa only [C,mul_assoc,add_comm] using add_le_add_left hb 1
  have hIb : ∀ᵐ z ∂ν,‖I z‖≤C := hIb₀.filter_mono hν.ae_le
  let P : Vector N×Vector N→Prop := fun z =>
    1≤Fa z ∧ ‖Fa z‖≤C ∧ 0≤Ua z ∧ Ua z≤1
  have hPm : MeasurableSet {z | P z} := by
    dsimp only [P]
    exact (measurableSet_le measurable_const hFm).inter
      ((measurableSet_le hFm.norm measurable_const).inter
        ((measurableSet_le measurable_const hUm).inter
          (measurableSet_le hUm measurable_const)))
  have hFUb : ∀ᵐ z ∂ν,P z := by
    exact ae_globalTilt_of_gibbs_fibres hN β H₀ hH₀ H hH
      P hPm (by
        intro v hv
        simpa only [P,Fa,Ua,H,C] using hphys v hv) w M
  have hR' : Integrable (fun z => PhysicalHitting.capKilling α z.1 z.2*Fa z) ν := by
    simpa only [Fa,ν,w,H,H₀,π,ν₀] using hRi
  have hK' : Integrable (fun z => (tiltDefect w z)^2*
      (∑ ij : Fin N×Fin N,(GFa ij z)^2/Fa z)) ν := by
    simpa only [GFa,Fa,ν,w,H,H₀,π,ν₀] using hKi
  have hB' : Integrable (fun z => Fa z*
      (∑ ij : Fin N×Fin N,(Ga ij z)^2)) ν := by
    simpa only [Ga,Fa,ν,w,H,H₀,π,ν₀] using hBi
  have hFb : ∀ᵐ z ∂ν,1≤Fa z ∧ ‖Fa z‖≤C :=
    hFUb.mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hUb : ∀ᵐ z ∂ν,0≤Ua z ∧ Ua z≤1 :=
    hFUb.mono (fun z hz => ⟨hz.2.2.1,hz.2.2.2⟩)
  have h := source_pair_integrable_of_energy ν I
    (fun z => PhysicalHitting.capKilling α z.1 z.2)
    (tiltDefect w) Fa Ua GFa Ga hk.measurable hFm hUm hGFm hGm
    C C hC hC hIb hFb hUb hIi hki hR' hK' hB'
  simpa only [I,Fa,Ua,GFa,Ga,ν,w,H,H₀,π,ν₀,mul_assoc] using h

end SlowEquilibration.ConditionedEntrance
