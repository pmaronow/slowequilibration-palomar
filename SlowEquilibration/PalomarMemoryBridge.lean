-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PalomarMemoryDefinitions
public import SlowEquilibration.PalomarHeatSpectralProjection
public import SlowEquilibration.SmoothRayleighEigenvalue
public import SixHeadlines

@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarMemory
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalPhysicalSpectral SphericalLaplaceIdentification SphericalCenteredObservables
open SphericalSpinProjection SphericalSpinCorrelation SphericalQuantitativeTrap
open SphericalMemoryAssembly PalomarCondensed
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

lemma source_transition_ae (hN : 1 ≤ N) (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    SlowEquilibrationCondensedSource.transitionLaw (SlowEquilibrationCondensedSource.field μ J) β t
      =ᵐ[SlowEquilibrationCondensedSource.gibbsLaw μ β J]
        mixedTransitionKernel (toLibrary μ) J β t := by
  filter_upwards [mixtureGibbsLaw_onSphere hN (toLibrary μ) J β] with x hx
  exact transitionLaw_eq_physical hN (toLibrary μ) J β t x hx

lemma source_joint_eq (hN : 1 ≤ N) (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    SlowEquilibrationCondensedSource.stationaryJointLaw μ β J t = twoTimeLaw (toLibrary μ) J β t := by
  let := mixtureGibbsLaw_probability hN (toLibrary μ) β J
  unfold SlowEquilibrationCondensedSource.stationaryJointLaw twoTimeLaw StationaryCoupling.law
  rw [Measure.compProd_eq_comp_prod]
  change _ = (mixtureGibbsLaw (toLibrary μ) β J).bind _
  apply Measure.bind_congr_right
  filter_upwards [source_transition_ae hN μ J β t] with x hx
  rw [hx, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]

lemma source_correlation_eq (hN : 1 ≤ N) (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    SlowEquilibrationCondensedSource.connectedSpinCorrelation μ β J t =
      connectedSpinCorrelation (toLibrary μ) J β t := by
  unfold SlowEquilibrationCondensedSource.connectedSpinCorrelation connectedSpinCorrelation
  rw [source_joint_eq hN μ J β t]
  rfl

lemma source_information_eq (hN : 1 ≤ N) (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    SlowEquilibrationCondensedSource.stationaryInformation μ β J t =
      endpointMutualInformation (mixtureGibbsLaw (toLibrary μ) β J)
        (mixedTransitionKernel (toLibrary μ) J β t) := by
  unfold SlowEquilibrationCondensedSource.stationaryInformation endpointMutualInformation
  rw [source_joint_eq hN μ J β t, mixedTransitionKernel_gibbs_invariant hN]
  rfl

lemma source_heatEigenfunction_iff (hN : 2 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β lam : ℝ)
    (u : Lp ℝ 2 (SlowEquilibrationCondensedSource.gibbsLaw μ β J)) :
    SlowEquilibrationCondensedSource.HeatEigenfunction μ β J lam u ↔
      ∀ t : ℝ≥0, (SphericalSpinProjection.data hN (toLibrary μ) J β).toSemigroupData.P t u =
        Real.exp (-(t : ℝ)*lam) • u := by
  have hN1 : 1 ≤ N := by omega
  have heq (t : ℝ≥0) :
      (SphericalSpinProjection.data hN (toLibrary μ) J β).toSemigroupData.P t u
        =ᵐ[mixtureGibbsLaw (toLibrary μ) β J]
          (fun x => ∫ y, u y ∂SlowEquilibrationCondensedSource.transitionLaw
            (SlowEquilibrationCondensedSource.field μ J) β t x) := by
    rw [← P_eq_diagonal]
    apply (SphericalL2Semigroup.P_ae hN1 (toLibrary μ) J β t u).trans
    filter_upwards [source_transition_ae hN1 μ J β t] with x hx
    rw [hx]
  constructor
  · intro hu t
    apply Lp.ext
    exact (heq t).trans ((hu t).trans (Lp.coeFn_smul (Real.exp (-(t : ℝ)*lam)) u).symm)
  · intro hu t
    have hh := heq t
    rw [hu t] at hh
    exact hh.symm.trans (Lp.coeFn_smul (Real.exp (-(t : ℝ)*lam)) u)

lemma source_lowSubspace_eq (hN : 2 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β Λ : ℝ) :
    SlowEquilibrationCondensedSource.lowSpectralSubspace μ β J Λ =
      (SphericalSpinProjection.data hN (toLibrary μ) J β).toSemigroupData.lowSubspace Λ := by
  let D := SphericalSpinProjection.data hN (toLibrary μ) J β
  rw [PalomarHeatSpectralProjection.lowSubspace_eq_closedSpan_heatEigenfunctions
    D.toSemigroupData D.generator_tendsto_atTop Λ]
  unfold SlowEquilibrationCondensedSource.lowSpectralSubspace
  congr 2
  ext u
  change (∃ lam : ℝ, 0 < lam ∧ lam ≤ Λ ∧
      SlowEquilibrationCondensedSource.HeatEigenfunction μ β J lam u) ↔
    (∃ lam : ℝ, 0 < lam ∧ lam ≤ Λ ∧
      ∀ t : ℝ≥0, (D.toSemigroupData.P t) u = Real.exp (-(t : ℝ)*lam) • u)
  simp only [source_heatEigenfunction_iff hN μ J β]
  rfl

lemma source_centeredSpinL2_eq (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β : ℝ) (i : Fin N) :
    SlowEquilibrationCondensedSource.centeredSpinL2 μ β J i =
      centeredL2 hN (toLibrary μ) J β SphericalBarycenter.spin
        (SphericalBarycenter.spin_contDiff.of_le (by simp)) i := by
  let f := SlowEquilibrationCondensedSource.centeredSpinCoordinate μ β J i
  let z := centeredL2 hN (toLibrary μ) J β SphericalBarycenter.spin
    (SphericalBarycenter.spin_contDiff.of_le (by simp)) i
  have hz : z =ᵐ[mixtureGibbsLaw (toLibrary μ) β J] f :=
    gibbsToL2_coe hN β (SphericalLaplaceIdentification.potential (toLibrary μ) J)
      (SphericalLaplaceIdentification.potential_continuous (toLibrary μ) J)
      (fun x => centered (toLibrary μ) J β SphericalBarycenter.spin x i)
      (SphericalForm.contDiff_vector_coordinate
        (centered_contDiff (toLibrary μ) J β
          (SphericalBarycenter.spin_contDiff.of_le (by simp))) i).continuous
  have hf : MemLp f 2 (SlowEquilibrationCondensedSource.gibbsLaw μ β J) :=
    (memLp_congr_ae hz).mp (Lp.memLp z)
  rw [SlowEquilibrationCondensedSource.centeredSpinL2, dite_eq_left hf]
  apply Lp.ext
  exact hf.coeFn_toLp.trans hz.symm

private lemma starProjection_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : K = L) :
    K.starProjection = L.starProjection := by
  subst L
  rfl

lemma source_projection_eq (hN : 2 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β Λ : ℝ) :
    SlowEquilibrationCondensedSource.spinProjectionMass μ β J Λ =
      ‖vectorCutoff hN (toLibrary μ) J β Λ
        (centeredL2 (show 1 ≤ N by omega) (toLibrary μ) J β SphericalBarycenter.spin
          (SphericalBarycenter.spin_contDiff.of_le (by simp)))‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold SlowEquilibrationCondensedSource.spinProjectionMass
  apply Finset.sum_congr rfl
  intro i _
  rw [starProjection_congr _ _ (source_lowSubspace_eq hN μ J β Λ)]
  rw [source_centeredSpinL2_eq (show 1 ≤ N by omega) μ J β i,
    ← (SphericalSpinProjection.data hN (toLibrary μ) J β).toSemigroupData.cutoff_eq_starProjection Λ]
  rfl

lemma source_eigenvalue_eq (hN : 2 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) (β : ℝ) (k : ℕ) :
    SlowEquilibrationCuspSource.rayleighEigenvalue (SlowEquilibrationCondensedSource.gibbsLaw μ β J) k =
      (normalizedSphericalSpectralData hN β (fieldOfMixture (toLibrary μ) J)
        (fieldOfMixture_contDiff (toLibrary μ) J).continuous).eigenvalue k := by
  exact PalomarCusp.literal_rayleigh_eq_eigenvalue hN β
    ((fieldOfMixture_contDiff (toLibrary μ) J).of_le (by simp)) _ k

lemma source_persistent_of_library {hN : 2 ≤ N}
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    {J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree} {β κ γ a c C : ℝ}
    (h : SphericalMemoryAssembly.PersistentMemoryConclusions hN (toLibrary μ) β J κ γ a c C) :
    SlowEquilibrationCondensedSource.PersistentMemoryConclusions μ β J κ γ a c C := by
  refine ⟨?_, ?_, ?_⟩
  · rw [source_eigenvalue_eq hN μ J β]
    exact h.eigenvalue
  · obtain ⟨X,hX,hXs,hMass,hTV⟩ := h.typicalStartingPoints
    refine ⟨X,hX,hXs,hMass,?_⟩
    intro x hx t ht
    rw [field_eq, transitionLaw_eq_physical (show 1 ≤ N by omega) (toLibrary μ) J β t x (hXs hx)]
    exact hTV x hx t (by simpa [SlowEquilibrationCondensedSource.exponentialHorizon,memoryTime,mul_comm] using ht)
  · intro t ht hT
    rw [source_information_eq (show 1 ≤ N by omega) μ J β t]
    exact h.stationaryInformation t ht (by simpa [SlowEquilibrationCondensedSource.exponentialHorizon,memoryTime,mul_comm] using hT)

lemma source_memory_of_library {hN : 2 ≤ N}
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    {J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree} {β b κ γ a c C : ℝ}
    (h : SphericalMemoryAssembly.MemoryConclusions hN (toLibrary μ) β J b κ γ a c C) :
    SlowEquilibrationCondensedSource.MemoryConclusions μ β J b κ γ a c C := by
  refine ⟨source_persistent_of_library μ (h.persistent le_rfl), ?_, ?_⟩
  · rw [source_projection_eq hN μ J β]
    exact h.spinProjection
  · intro t ht
    rw [source_correlation_eq (show 1 ≤ N by omega) μ J β t]
    exact h.connectedCorrelation t (by simpa [SlowEquilibrationCondensedSource.exponentialHorizon,memoryTime,mul_comm] using ht)

theorem theorem_1_5 (μ : SlowEquilibrationCondensedSource.FiniteMixture) {β b : ℝ}
    (hβd : SlowEquilibrationCondensedSource.dynamicalThreshold μ.xi < β)
    (hβs : β < SlowEquilibrationCondensedSource.staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) ((SlowEquilibrationCondensedSource.qStar μ.xi β)^2)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (SlowEquilibrationCondensedSource.Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree).real Ωᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ J ∈ Ω, ∀ _hN : 2 ≤ N,
          SlowEquilibrationCondensedSource.MemoryConclusions μ β J b κ γ a c C := by
  obtain ⟨κ,γ,a,c,C,hκ,hγ,ha,hc,hC,h⟩ :=
    SixHeadlines.theorem_1_5 (toLibrary μ) hβd hβs hb
  refine ⟨κ,γ,a,c,C,hκ,hγ,ha,hc,hC,?_⟩
  filter_upwards [h] with N hN
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN
  exact ⟨Ω,hΩ,hfail,fun J hJ hN => source_memory_of_library μ (hgood J hJ hN)⟩

theorem theorem_1_6 (μ : SlowEquilibrationCondensedSource.FiniteMixture) {β b : ℝ}
    (hβd : SlowEquilibrationCondensedSource.dynamicalThreshold μ.xi < β)
    (hβs : β < SlowEquilibrationCondensedSource.staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) (SlowEquilibrationCondensedSource.qStar μ.xi β)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      (∀ᶠ N : ℕ in atTop, ∃ Ω₀ : Set (SlowEquilibrationCondensedSource.Disorder N μ.maxDegree), MeasurableSet Ω₀ ∧
        (SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree).real Ω₀ᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ J ∈ Ω₀, ∀ _hN : 2 ≤ N,
          SlowEquilibrationCondensedSource.PersistentMemoryConclusions μ β J κ γ a c C) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
        ∃ Ω : Set (SlowEquilibrationCondensedSource.Disorder N μ.maxDegree), MeasurableSet Ω ∧
          (SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree).real Ωᶜ < η ∧
          ∀ J ∈ Ω, ∀ _hN : 2 ≤ N,
            SlowEquilibrationCondensedSource.MemoryConclusions μ β J b κ γ a c C) := by
  obtain ⟨κ,γ,a,c,C,hκ,hγ,ha,hc,hC,hp,hm⟩ :=
    SixHeadlines.theorem_1_6 (toLibrary μ) hβd hβs hb
  refine ⟨κ,γ,a,c,C,hκ,hγ,ha,hc,hC,?_,?_⟩
  · filter_upwards [hp] with N hN
    obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN
    exact ⟨Ω,hΩ,hfail,fun J hJ hN => source_persistent_of_library μ (hgood J hJ hN)⟩
  · intro η hη
    filter_upwards [hm η hη] with N hN
    obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN
    exact ⟨Ω,hΩ,hfail,fun J hJ hN => source_memory_of_library μ (hgood J hJ hN)⟩

end SlowEquilibration.PalomarMemory
