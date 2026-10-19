-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceGlobalRawEnergy
public import SlowEquilibration.ConditionedEntranceSignedGlobalAllEnergy
public import SlowEquilibration.ConditionedEntranceSourceGlobalBounds

/-! The actual source joint resolvents and their completed gradients
satisfy one global signed raw energy inequality under the physical
axis–spin tilt. The two square commutator moments and the a.e. bounds
are retained for the subsequent numerical absorption. -/
@[expose] public section
noncomputable section
open MeasureTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_joint_signed_global_raw_energy_physical_graph_pair_witness
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (J : Disorder N μ.maxDegree) (hJ : J ∈ regularDisorder)
    (e k hbar kbar B R : ℝ) (hh : |e| ≤ hbar) (hk : |k| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s, |χ s| ≤ B) (hχR : ∀ s, R < |s| → χ s = 0)
    (M : ℝ) (hM : 0 < M)
    (hMphys : M = ∫ z : Vector N×Vector N,
      Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
        fieldOfMixture μ J z.2))
      ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))) :
    let H₀ := fieldOfMixture μ J
    let w : Vector N×Vector N → ℝ := fun z =>
      β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    ∃ F : SourceParameters N μ×Vector N→ℝ,
    ∃ GF : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
    ∃ U : SourceParameters N μ×Vector N→ℝ,
    ∃ G : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
    ∃ F₀ : sphericalSobolevGraph hN β H₀
      (fieldOfMixture_contDiff μ J).continuous,
      let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
      let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
      let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
        GF ij ((J,(z.1,(e,k))),z.2)
      let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
        G ij ((J,(z.1,(e,k))),z.2)
      (fun x => F ((J,((0 : Vector N),(e,k))),x)) =ᵐ[gibbsLaw N β H₀]
        F₀.val.fst ∧
      (∀ ij : Fin N×Fin N,
        (fun x => GF ij ((J,((0 : Vector N),(e,k))),x)) =ᵐ[gibbsLaw N β H₀]
          F₀.val.snd ij) ∧
      (∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F₀.val.fst x) ∧
      (∫ x, F ((J,((0 : Vector N),(e,k))),x)
        ∂gibbsLaw N β H₀) = 2 ∧
      sphericalFisher hN β H₀ (fieldOfMixture_contDiff μ J).continuous F₀ ≤
        (θ : ℝ)*(2*Real.log 2+
          4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
      (∀ v : Vector N, ∀ hv : OnSphere v,
        let p : SourceParameters N μ := (J,(v,(e,k)))
        let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
          α hα χ hχ p hv
        ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          referenceRate D.baseData β θ (referenceInitialVector D.baseData β)) ∧
        ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          rateLaplace D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous
            (PhysicalHitting.capKilling_nonneg α v) θ
            (killingVector D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous))) ∧
      (∀ v : Vector N, ∀ hv : OnSphere v,
        let p : SourceParameters N μ := (J,(v,(e,k)))
        let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
          α hα χ hχ p hv
        ∃ Fb : sphericalSobolevGraph hN β D.baseData.hamiltonian
            D.baseData.hamiltonian_contDiff.continuous,
        ∃ u : sphericalSobolevGraph hN β D.hamiltonian
            D.hamiltonian_contDiff.continuous,
          sphericalEnergyL2Map hN β D.baseData.hamiltonian
            D.baseData.hamiltonian_contDiff.continuous Fb =
              referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
          sphericalEnergyL2Map hN β D.hamiltonian
            D.hamiltonian_contDiff.continuous u =
              rateLaplace D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous
                (PhysicalHitting.capKilling_nonneg α v) θ
                (killingVector D β (PhysicalHitting.capKilling α v)
                  (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
          ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D.baseData.hamiltonian]
            Fb.val.fst) ∧
          (∀ ij : Fin N×Fin N,
            (fun x => GF ij (p,x)) =ᵐ[gibbsLaw N β D.baseData.hamiltonian]
              Fb.val.snd ij) ∧
          ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
            u.val.fst) ∧
          ∀ ij : Fin N×Fin N,
            (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
              u.val.snd ij) ∧
      (∀ v : Vector N, OnSphere v →
        ∀ᵐ x ∂gibbsLaw N β
          (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ),
          1≤F ((J,(v,(e,k))),x) ∧
          ‖F ((J,(v,(e,k))),x)‖≤
            1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
          0≤U ((J,(v,(e,k))),x) ∧ U ((J,(v,(e,k))),x)≤1) ∧
      StronglyMeasurable F ∧ (∀ ij, StronglyMeasurable (GF ij)) ∧
      StronglyMeasurable U ∧ (∀ ij, StronglyMeasurable (G ij)) ∧
      (∀ p q x, p.1=q.1 → F (p,x)=F (q,x)) ∧
      (∀ ij p q x, p.1=q.1 → GF ij (p,x)=GF ij (q,x)) ∧
      (∀ᵐ z ∂ν, 1 ≤ Fa z ∧ 0 ≤ Ua z ∧ Ua z ≤ 1) ∧
      Integrable (fun z => Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2)) ν ∧
      Integrable (fun z => (tiltDefect w z)^2*(Fa z-1)) ν ∧
      Integrable (fun z => (tiltDefect w z)^2*
        (∑ ij : Fin N×Fin N,(GFa ij z)^2/Fa z)) ν ∧
      Integrable (fun z => Fa z*Ua z^2) ν ∧
      Integrable (fun z => PhysicalHitting.capKilling α z.1 z.2*Fa z) ν ∧
      Integrable (fun z => tiltDefect w z*(Fa z-1)*Ua z^2) ν ∧
      Integrable (fun z => tiltDefect w z*Ua z*
        (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z)) ν ∧
      (∫ z, Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2) ∂ν)+
        (θ : ℝ)/2*(∫ z, Fa z*Ua z^2 ∂ν) ≤
        (∫ z, PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)+
        (θ : ℝ)/2*|∫ z, tiltDefect w z*(Fa z-1)*Ua z^2 ∂ν|+
        |∫ z, tiltDefect w z*Ua z*
          (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z) ∂ν| := by
  dsimp only
  obtain ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,_hBm,_hAm,_hKm,_hRm,_hCm,_hJm,
    hE,hBi,hKi,hJi,hAi,hRi,hKsi,hCsi⟩ :=
    sourceJointReferenceSignedReducedEnergy_globalAllEnergyIntegrable hN μ hnp Q hQ hQ1
      α hα χ hχ β hβ θ hθ J hJ e k hbar kbar B R hh hk hB hR hχB hχR M hM
  let H₀ := fieldOfMixture μ J
  let w : Vector N×Vector N → ℝ := fun z =>
    β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
  let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
  let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
  let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,k))),z.2)
  let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    G ij ((J,(z.1,(e,k))),z.2)
  have hphys (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β
        (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ),
        1 ≤ F ((J,(v,(e,k))),x) ∧
        0 ≤ U ((J,(v,(e,k))),x) ∧
        U ((J,(v,(e,k))),x) ≤ 1 := by
    obtain ⟨_hFs,_hUs,hFb,hUb,_hFisher,_hEnergy,_hGraph⟩ :=
      hE (J,(v,(e,k))) hv hJ
    filter_upwards [hFb,hUb] with x hf hu
    exact ⟨hf.1,hu.1,hu.2⟩
  have hbounds := source_joint_reference_globalTilt_bounds hN μ hnp Q hQ
    α χ hχ.continuous β J e k F U hF hU hphys M
  have hBfibre (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N μ := (J,(v,(e,k)))
      jointGibbsWeightedGradientSquare β
        (sourceJointHamiltonian μ Q hQ hnp α χ) F G p =
        ∫ x, F (p,x)*(∑ ij : Fin N×Fin N,(G ij (p,x))^2)
          ∂gibbsLaw N β
            (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ) := by
    dsimp only
    let p : SourceParameters N μ := (J,(v,(e,k)))
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
      α hα χ hχ p hv
    obtain ⟨_hFs,_hUs,hFb,_hUb,_hFisher,_hEnergy,hGraph⟩ := hE p hv hJ
    obtain ⟨F₀,F₁,u,_hF₀,_hu,_hFF₀,_hGF₀,hFF₁,_hGF₁,_hUv,hGv⟩ := hGraph
    let CF : ℝ≥0 := ⟨1+Real.exp
      (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)), by positivity⟩
    have hF₁b : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
        1 ≤ F₁.val.fst x ∧ ‖F₁.val.fst x‖ ≤ CF := by
      filter_upwards [hFb,hFF₁] with x hb hf
      rw [hf] at hb
      refine ⟨hb.1, ?_⟩
      change ‖F₁.val.fst x‖ ≤
        1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))
      exact hb.2
    exact source_joint_weighted_gradient_fibre_integral hN μ hnp Q hQ hQ1
      α hα χ hχ β p hv F G hF hG F₁ u CF hF₁b hFF₁ hGv
  have hpoint (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let H := sourceJointHamiltonian μ Q hQ hnp α χ
      let H₀ := fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2
      let w := fun z => β*H z-β*H₀ z
      let κ := sourceJointCapKilling μ α
      jointGibbsWeightedGradientSquare β H F G p+
        (θ : ℝ)/2*jointGibbsWeightedSquare β H F U p ≤
          jointGibbsKilledReference β H κ F p-
          (θ : ℝ)/2*jointGibbsZeroDefectSquare β H w F U p-
          jointGibbsTiltGradientCross β H w U GF G p := by
    dsimp only
    exact (hE (J,(v,(e,k))) hv hJ).2.2.2.2.2.1
  have hraw := source_joint_signed_global_raw_energy_of_fibres hN μ hnp Q hQ
    α χ hχ.continuous β θ J e k F U GF G M hM hMphys
    hBi hAi hRi hKsi hCsi hBfibre hpoint
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  obtain ⟨v₀,hv₀s⟩ := (sphereLaw_support hN).exists
  have hv₀ : OnSphere v₀ := (onSphere_iff_norm_sq v₀).mpr hv₀s
  let p₀ : SourceParameters N μ := (J,(v₀,(e,k)))
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
    α hα χ hχ p₀ hv₀
  obtain ⟨_hFs,_hUs,hFb,_hUb,hFisher,_hEnergy,hGraph⟩ := hE p₀ hv₀ hJ
  obtain ⟨F₀,_F₁,_u,hF₀,_hu,hFF₀,hGF₀,_hFF₁,_hGF₁,_hUv,_hGv⟩ := hGraph
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  obtain ⟨F₀',hFval,hFgrad⟩ := sphericalSobolevGraph_changeGibbs hN β β
    D.baseData.hamiltonian H₀ D.baseData.hamiltonian_contDiff.continuous hH₀ F₀
  have hπ : gibbsLaw N β D.baseData.hamiltonian =
      gibbsLaw N β H₀ := by
    rw [D.baseData_hamiltonian]
    rfl
  have hAC : ae (gibbsLaw N β D.baseData.hamiltonian) ≤
      ae (gibbsLaw N β D.hamiltonian) :=
    (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D.hamiltonian
      D.baseData.hamiltonian D.hamiltonian_contDiff.continuous).ae_le
  have hFb₀ : ∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F (p₀,x) := by
    simpa only [hπ] using (hFb.filter_mono hAC).mono (fun _ hx => hx.1)
  have hFF₀' : (fun x => F (p₀,x)) =ᵐ[gibbsLaw N β H₀] F₀.val.fst := by
    rw [← hπ]
    exact hFF₀
  have hF₀lo : ∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F₀'.val.fst x := by
    filter_upwards [hFb₀,hFF₀',hFval] with x hb hff hf
    rw [hff] at hb
    rw [hf]
    exact hb
  have hFp₀ : (fun x => F (p₀,x)) =ᵐ[gibbsLaw N β H₀]
      F₀'.val.fst := hFF₀'.trans hFval.symm
  have hGFp₀ (ij : Fin N×Fin N) :
      (fun x => GF ij (p₀,x)) =ᵐ[gibbsLaw N β H₀]
        F₀'.val.snd ij := by
    have hg : (fun x => GF ij (p₀,x)) =ᵐ[gibbsLaw N β H₀]
        F₀.val.snd ij := by
      rw [← hπ]
      exact hGF₀ ij
    exact hg.trans (hFgrad ij).symm
  have hFrep : (fun x => F ((J,((0 : Vector N),(e,k))),x)) =ᵐ[
      gibbsLaw N β H₀] F₀'.val.fst := by
    filter_upwards [hFp₀] with x hx
    rw [hFf (J,((0 : Vector N),(e,k))) p₀ x rfl]
    exact hx
  have hGFrep (ij : Fin N×Fin N) :
      (fun x => GF ij ((J,((0 : Vector N),(e,k))),x)) =ᵐ[
        gibbsLaw N β H₀] F₀'.val.snd ij := by
    filter_upwards [hGFp₀ ij] with x hx
    rw [hGFf ij (J,((0 : Vector N),(e,k))) p₀ x rfl]
    exact hx
  have hFmass : (∫ x, F ((J,((0 : Vector N),(e,k))),x)
      ∂gibbsLaw N β H₀) = 2 := by
    have hFref : (fun x => F ((J,((0 : Vector N),(e,k))),x)) =ᵐ[
        gibbsLaw N β H₀]
        referenceRate D.baseData β θ (referenceInitialVector D.baseData β) := by
      have hfv : F₀.val.fst =
          referenceRate D.baseData β θ (referenceInitialVector D.baseData β) := hF₀
      filter_upwards [hFF₀'] with x hx
      rw [hFf (J,((0 : Vector N),(e,k))) p₀ x rfl, hx, hfv]
    rw [integral_congr_ae hFref, ← hπ]
    rw [referenceRate_mass D.baseData β θ hθ
      (referenceInitialVector D.baseData β)]
    exact referenceInitialVector_mass D.baseData β
  have hJFp : jointGibbsFisher β
      (fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2)
      F GF p₀ =
      sphericalFisher hN β H₀ hH₀ F₀' := by
    unfold jointGibbsFisher sphericalFisher
    apply Finset.sum_congr rfl
    intro ij _
    apply integral_congr_ae
    filter_upwards [hFp₀,hGFp₀ ij] with x hf hg
    rw [hf,hg,div_eq_mul_inv]
  have hJF : sphericalFisher hN β H₀ hH₀ F₀' ≤
      (θ : ℝ)*(2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) := by
    rw [← hJFp]
    exact hFisher
  have hPhysical (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
        α hα χ hχ p hv
      ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
        referenceRate D.baseData β θ (referenceInitialVector D.baseData β)) ∧
      ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
        rateLaplace D β (PhysicalHitting.capKilling α v)
          (PhysicalHitting.capKilling_contDiff α v).continuous
          (PhysicalHitting.capKilling_nonneg α v) θ
          (killingVector D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous)) := by
    dsimp only
    obtain ⟨hFs,hUs,_hFb,_hUb,_hFisher,_hEnergy,_hGraph⟩ :=
      hE (J,(v,(e,k))) hv hJ
    exact ⟨hFs,hUs⟩
  have hPairGraph (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
        α hα χ hχ p hv
      ∃ Fb : sphericalSobolevGraph hN β D.baseData.hamiltonian
          D.baseData.hamiltonian_contDiff.continuous,
      ∃ u : sphericalSobolevGraph hN β D.hamiltonian
          D.hamiltonian_contDiff.continuous,
        sphericalEnergyL2Map hN β D.baseData.hamiltonian
          D.baseData.hamiltonian_contDiff.continuous Fb =
            referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
        sphericalEnergyL2Map hN β D.hamiltonian
          D.hamiltonian_contDiff.continuous u =
            rateLaplace D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous
              (PhysicalHitting.capKilling_nonneg α v) θ
              (killingVector D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
        ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D.baseData.hamiltonian]
          Fb.val.fst) ∧
        (∀ ij : Fin N×Fin N,
          (fun x => GF ij (p,x)) =ᵐ[gibbsLaw N β D.baseData.hamiltonian]
            Fb.val.snd ij) ∧
        ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          u.val.fst) ∧
        ∀ ij : Fin N×Fin N,
          (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
            u.val.snd ij := by
    dsimp only
    obtain ⟨_hFs,_hUs,_hFb,_hUb,_hFisher,_hEnergy,hGraph⟩ :=
      hE (J,(v,(e,k))) hv hJ
    obtain ⟨Fb,_F₁,u,hFb,hu,hFrep',hGFrep',_hFcur,_hGFcur,
      hUcur,hGcur⟩ := hGraph
    exact ⟨Fb,u,hFb,hu,hFrep',hGFrep',hUcur,hGcur⟩
  have hPhysBound (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β
        (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ),
        1≤F ((J,(v,(e,k))),x) ∧
        ‖F ((J,(v,(e,k))),x)‖≤
          1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
        0≤U ((J,(v,(e,k))),x) ∧ U ((J,(v,(e,k))),x)≤1 := by
    obtain ⟨_hFs,_hUs,hFb,hUb,_hFisher,_hEnergy,_hGraph⟩ :=
      hE (J,(v,(e,k))) hv hJ
    filter_upwards [hFb,hUb] with x hf hu
    exact ⟨hf.1,hf.2,hu.1,hu.2⟩
  exact ⟨F,GF,U,G,F₀',hFrep,hGFrep,hF₀lo,hFmass,hJF,hPhysical,hPairGraph,hPhysBound,
    hF,hGF,hU,hG,hFf,hGFf,hbounds,hBi,hKi,hJi,
    hAi,hRi,hKsi,hCsi,hraw⟩

end SlowEquilibration.ConditionedEntrance
