-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureGlobalRawEnergy
public import SlowEquilibration.ConditionedEntrancePureSignedGlobalAllEnergy
public import SlowEquilibration.ConditionedEntrancePureGlobalBounds

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
open SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 800000

set_option linter.unusedVariables false in
theorem pure_joint_signed_global_raw_energy_physical_graph_pair_witness
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (hJ : J ∈ regularDisorder)
    (e : ℝ)
    (M : ℝ) (hM : 0 < M)
    (hMphys : M = ∫ z : Vector N×Vector N,
      Real.exp (β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
        fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2))
      ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))) :
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let w : Vector N×Vector N → ℝ := fun z =>
      β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    ∃ F : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ,
    ∃ GF : (Fin N×Fin N)→SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ,
    ∃ U : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ,
    ∃ G : (Fin N×Fin N)→SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ,
    ∃ F₀ : sphericalSobolevGraph hN β H₀
      (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous,
      let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
      let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
      let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
        GF ij ((J,(z.1,(e,0))),z.2)
      let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
        G ij ((J,(z.1,(e,0))),z.2)
      (fun x => F ((J,((0 : Vector N),(e,0))),x)) =ᵐ[gibbsLaw N β H₀]
        F₀.val.fst ∧
      (∀ ij : Fin N×Fin N,
        (fun x => GF ij ((J,((0 : Vector N),(e,0))),x)) =ᵐ[gibbsLaw N β H₀]
          F₀.val.snd ij) ∧
      (∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F₀.val.fst x) ∧
      (∫ x, F ((J,((0 : Vector N),(e,0))),x)
        ∂gibbsLaw N β H₀) = 2 ∧
      sphericalFisher hN β H₀ (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous F₀ ≤
        (θ : ℝ)*(2*Real.log 2+
          4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) ∧
      (∀ v : Vector N, ∀ hv : OnSphere v,
        let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
        let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
        let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p.1
        ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          referenceRate D₀ β θ (referenceInitialVector D₀ β)) ∧
        ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          rateLaplace D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous
            (PhysicalHitting.capKilling_nonneg α v) θ
            (killingVector D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous))) ∧
      (∀ v : Vector N, ∀ hv : OnSphere v,
        let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
        let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
        let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p.1
        ∃ Fb : sphericalSobolevGraph hN β D₀.hamiltonian
            D₀.hamiltonian_contDiff.continuous,
        ∃ u : sphericalSobolevGraph hN β D.hamiltonian
            D.hamiltonian_contDiff.continuous,
          sphericalEnergyL2Map hN β D₀.hamiltonian
            D₀.hamiltonian_contDiff.continuous Fb =
              referenceRate D₀ β θ (referenceInitialVector D₀ β) ∧
          sphericalEnergyL2Map hN β D.hamiltonian
            D.hamiltonian_contDiff.continuous u =
              rateLaplace D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous
                (PhysicalHitting.capKilling_nonneg α v) θ
                (killingVector D β (PhysicalHitting.capKilling α v)
                  (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
          ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D₀.hamiltonian]
            Fb.val.fst) ∧
          (∀ ij : Fin N×Fin N,
            (fun x => GF ij (p,x)) =ᵐ[gibbsLaw N β D₀.hamiltonian]
              Fb.val.snd ij) ∧
          ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
            u.val.fst) ∧
          ∀ ij : Fin N×Fin N,
            (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
              u.val.snd ij) ∧
      (∀ v : Vector N, OnSphere v →
        ∀ᵐ x ∂gibbsLaw N β
          (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
          1≤F ((J,(v,(e,0))),x) ∧
          ‖F ((J,(v,(e,0))),x)‖≤
            1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) ∧
          0≤U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x)≤1) ∧
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
    pureJointReferenceSignedReducedEnergy_globalAllEnergyIntegrable hN d hd c hc Q
      α hα χ hχ β hβ θ hθ J hJ e M hM
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let w : Vector N×Vector N → ℝ := fun z =>
    β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-H₀ z.2)
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
  let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
  let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
  let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,0))),z.2)
  let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    G ij ((J,(z.1,(e,0))),z.2)
  have hphys (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β
        (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
        1 ≤ F ((J,(v,(e,0))),x) ∧
        0 ≤ U ((J,(v,(e,0))),x) ∧
        U ((J,(v,(e,0))),x) ≤ 1 := by
    obtain ⟨_hFs,_hUs,hFb,hUb,_hFisher,_hEnergy,_hGraph⟩ :=
      hE (J,(v,(e,0))) hv hJ
    simp only [FieldData.ofPure_hamiltonian] at hFb hUb
    filter_upwards [hFb,hUb] with x hf hu
    exact ⟨hf.1,hu.1,hu.2⟩
  have hbounds := pure_joint_reference_globalTilt_bounds hN d hd c hc Q
    α χ hχ β J e F U hF hU hphys M
  have hBfibre (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      jointGibbsWeightedGradientSquare β
        (pureSourceJointHamiltonian d hd c hc Q α χ) F G p =
        ∫ x, F (p,x)*(∑ ij : Fin N×Fin N,(G ij (p,x))^2)
          ∂gibbsLaw N β
            (pureSourceSmoothCutoffField d hd c hc Q J v e α χ) := by
    dsimp only
    let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
    let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
    let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p.1
    obtain ⟨_hFs,_hUs,hFb,_hUb,_hFisher,_hEnergy,hGraph⟩ := hE p hv hJ
    obtain ⟨F₀,F₁,u,_hF₀,_hu,_hFF₀,_hGF₀,hFF₁,_hGF₁,_hUv,hGv⟩ := hGraph
    let CF : ℝ≥0 := ⟨1+Real.exp
      (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)), by positivity⟩
    have hF₁b : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
        1 ≤ F₁.val.fst x ∧ ‖F₁.val.fst x‖ ≤ CF := by
      filter_upwards [hFb,hFF₁] with x hb hf
      rw [hf] at hb
      refine ⟨hb.1, ?_⟩
      change ‖F₁.val.fst x‖ ≤
        1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ))
      exact hb.2
    simpa only [FieldData.ofPure_hamiltonian] using
      pure_joint_weighted_gradient_fibre_integral hN d hd c hc Q
        α hα χ hχ β p hv F G hF hG F₁ u CF hF₁b hFF₁ hGv
  have hpoint (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      let H := pureSourceJointHamiltonian d hd c hc Q α χ
      let H₀ := fun z : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N => fieldOfMixture (FiniteMixture.pure d hd c hc) z.1.1 z.2
      let w := fun z => β*H z-β*H₀ z
      let κ := sourceJointCapKilling (FiniteMixture.pure d hd c hc) α
      jointGibbsWeightedGradientSquare β H F G p+
        (θ : ℝ)/2*jointGibbsWeightedSquare β H F U p ≤
          jointGibbsKilledReference β H κ F p-
          (θ : ℝ)/2*jointGibbsZeroDefectSquare β H w F U p-
          jointGibbsTiltGradientCross β H w U GF G p := by
    dsimp only
    exact (hE (J,(v,(e,0))) hv hJ).2.2.2.2.2.1
  have hraw := pure_joint_signed_global_raw_energy_of_fibres hN d hd c hc Q
    α χ hχ β θ J e F U GF G M hM hMphys
    hBi hAi hRi hKsi hCsi hBfibre hpoint
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  obtain ⟨v₀,hv₀s⟩ := (sphereLaw_support hN).exists
  have hv₀ : OnSphere v₀ := (onSphere_iff_norm_sq v₀).mpr hv₀s
  let p₀ : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v₀,(e,0)))
  let D := FieldData.ofPure hN d hd c hc Q p₀.1 p₀.2.1 p₀.2.2.1 α χ hχ
  let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p₀.1
  obtain ⟨_hFs,_hUs,hFb,_hUb,hFisher,_hEnergy,hGraph⟩ := hE p₀ hv₀ hJ
  obtain ⟨F₀,_F₁,_u,hF₀,_hu,hFF₀,hGF₀,_hFF₁,_hGF₁,_hUv,_hGv⟩ := hGraph
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  obtain ⟨F₀',hFval,hFgrad⟩ := sphericalSobolevGraph_changeGibbs hN β β
    D₀.hamiltonian H₀ D₀.hamiltonian_contDiff.continuous hH₀ F₀
  have hπ : gibbsLaw N β D₀.hamiltonian =
      gibbsLaw N β H₀ := by
    rfl
  have hAC : ae (gibbsLaw N β D₀.hamiltonian) ≤
      ae (gibbsLaw N β D.hamiltonian) :=
    (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D.hamiltonian
      D₀.hamiltonian D.hamiltonian_contDiff.continuous).ae_le
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
  have hFrep : (fun x => F ((J,((0 : Vector N),(e,0))),x)) =ᵐ[
      gibbsLaw N β H₀] F₀'.val.fst := by
    filter_upwards [hFp₀] with x hx
    rw [hFf (J,((0 : Vector N),(e,0))) p₀ x rfl]
    exact hx
  have hGFrep (ij : Fin N×Fin N) :
      (fun x => GF ij ((J,((0 : Vector N),(e,0))),x)) =ᵐ[
        gibbsLaw N β H₀] F₀'.val.snd ij := by
    filter_upwards [hGFp₀ ij] with x hx
    rw [hGFf ij (J,((0 : Vector N),(e,0))) p₀ x rfl]
    exact hx
  have hFmass : (∫ x, F ((J,((0 : Vector N),(e,0))),x)
      ∂gibbsLaw N β H₀) = 2 := by
    have hFref : (fun x => F ((J,((0 : Vector N),(e,0))),x)) =ᵐ[
        gibbsLaw N β H₀]
        referenceRate D₀ β θ (referenceInitialVector D₀ β) := by
      have hfv : F₀.val.fst =
          referenceRate D₀ β θ (referenceInitialVector D₀ β) := hF₀
      filter_upwards [hFF₀'] with x hx
      rw [hFf (J,((0 : Vector N),(e,0))) p₀ x rfl, hx, hfv]
    rw [integral_congr_ae hFref, ← hπ]
    rw [referenceRate_mass D₀ β θ hθ
      (referenceInitialVector D₀ β)]
    exact referenceInitialVector_mass D₀ β
  have hJFp : jointGibbsFisher β
      (fun z : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N => fieldOfMixture (FiniteMixture.pure d hd c hc) z.1.1 z.2)
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
        4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) := by
    rw [← hJFp]
    exact hFisher
  have hPhysical (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
      let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p.1
      ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
        referenceRate D₀ β θ (referenceInitialVector D₀ β)) ∧
      ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
        rateLaplace D β (PhysicalHitting.capKilling α v)
          (PhysicalHitting.capKilling_contDiff α v).continuous
          (PhysicalHitting.capKilling_nonneg α v) θ
          (killingVector D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous)) := by
    dsimp only
    obtain ⟨hFs,hUs,_hFb,_hUb,_hFisher,_hEnergy,_hGraph⟩ :=
      hE (J,(v,(e,0))) hv hJ
    exact ⟨hFs,hUs⟩
  have hPairGraph (v : Vector N) (hv : OnSphere v) :
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
      let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p.1
      ∃ Fb : sphericalSobolevGraph hN β D₀.hamiltonian
          D₀.hamiltonian_contDiff.continuous,
      ∃ u : sphericalSobolevGraph hN β D.hamiltonian
          D.hamiltonian_contDiff.continuous,
        sphericalEnergyL2Map hN β D₀.hamiltonian
          D₀.hamiltonian_contDiff.continuous Fb =
            referenceRate D₀ β θ (referenceInitialVector D₀ β) ∧
        sphericalEnergyL2Map hN β D.hamiltonian
          D.hamiltonian_contDiff.continuous u =
            rateLaplace D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous
              (PhysicalHitting.capKilling_nonneg α v) θ
              (killingVector D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
        ((fun x => F (p,x)) =ᵐ[gibbsLaw N β D₀.hamiltonian]
          Fb.val.fst) ∧
        (∀ ij : Fin N×Fin N,
          (fun x => GF ij (p,x)) =ᵐ[gibbsLaw N β D₀.hamiltonian]
            Fb.val.snd ij) ∧
        ((fun x => U (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          u.val.fst) ∧
        ∀ ij : Fin N×Fin N,
          (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
            u.val.snd ij := by
    dsimp only
    obtain ⟨_hFs,_hUs,_hFb,_hUb,_hFisher,_hEnergy,hGraph⟩ :=
      hE (J,(v,(e,0))) hv hJ
    obtain ⟨Fb,_F₁,u,hFb,hu,hFrep',hGFrep',_hFcur,_hGFcur,
      hUcur,hGcur⟩ := hGraph
    exact ⟨Fb,u,hFb,hu,hFrep',hGFrep',hUcur,hGcur⟩
  have hPhysBound (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β
        (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
        1≤F ((J,(v,(e,0))),x) ∧
        ‖F ((J,(v,(e,0))),x)‖≤
          1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) ∧
        0≤U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x)≤1 := by
    obtain ⟨_hFs,_hUs,hFb,hUb,_hFisher,_hEnergy,_hGraph⟩ :=
      hE (J,(v,(e,0))) hv hJ
    simp only [FieldData.ofPure_hamiltonian] at hFb hUb
    filter_upwards [hFb,hUb] with x hf hu
    exact ⟨hf.1,hf.2,hu.1,hu.2⟩
  exact ⟨F,GF,U,G,F₀',hFrep,hGFrep,hF₀lo,hFmass,hJF,hPhysical,hPairGraph,hPhysBound,
    hF,hGF,hU,hG,hFf,hGFf,hbounds,hBi,hKi,hJi,
    hAi,hRi,hKsi,hCsi,hraw⟩

end SlowEquilibration.ConditionedEntrance
