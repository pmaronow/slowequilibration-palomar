-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteSpectralTruncation
public import SlowEquilibration.SphericalInfiniteCutoffLaw

/-! Exponentially accurate transfer of the actual ordered spectra from a
canonical finite tensor cutoff to the original infinite Gaussian field. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem tailSphere_measurable {N : ℕ} (μ : InfiniteMixture) (P : ℕ) :
    Measurable (tailSphere (N := N) μ P) := by
  unfold tailSphere tailContinuous
  exact (sphereRestriction N).continuous.measurable.comp
    (Measurable.tsum fun q => (blockContinuous_continuous μ (q+P)).measurable)

theorem tailSphere_fixed_exponential_rate_eventually (μ : InfiniteMixture) {h : ℝ} (hh : 0<h) :
    ∀ᶠ P in atTop,∃ a : ℝ,0<a ∧ ∀ N : ℕ,0<N →
      (disorderLaw N).real {J|h*N<‖tailSphere μ P J‖}≤2*Real.exp (-a*N) := by
  filter_upwards [tailSphere_small_probability_eventually μ hh] with P hP
  by_cases hv : tailVariance μ P=0
  · refine ⟨1,by norm_num,?_⟩
    intro N hN
    have hh := hP N hN
    rw [if_pos hv] at hh
    have hz := le_antisymm hh (by positivity)
    rw [measureReal_def,hz,ENNReal.toReal_zero]
    positivity
  · refine ⟨h^2/(8*tailVariance μ P),by have := lt_of_le_of_ne (tailVariance_nonneg μ P) (Ne.symm hv); positivity,?_⟩
    intro N hN
    have hb := hP N hN
    rw [if_neg hv] at hb
    have hr := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hb
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    convert hr using 1 <;> congr 2 <;> ring

private theorem spectral_eigenvalue_congr {N : ℕ} (hN : 2≤N) (β : ℝ)
    (H G : Vector N → ℝ) (hH : Continuous H) (hG : Continuous G) (he : H=G) (k : ℕ) :
    (normalizedSphericalSpectralData hN β H hH).eigenvalue k=
      (normalizedSphericalSpectralData hN β G hG).eigenvalue k := by
  subst G
  rfl

/-- A spectral estimate at a fixed actual cutoff transfers to the literal
infinite field with only the proved oscillation loss and tail probability. -/
theorem infinite_spectral_transfer (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) {β h κ σ a b C : ℝ}
    (hβ : 0≤β) (ha : 0<a) (hb : 0<b) (hC : 0≤C)
    (htail : ∀ N : ℕ,0<N → (disorderLaw N).real
      {J|h*N<‖tailSphere μ (P-1) J‖}≤2*Real.exp (-b*N))
    (hfinite : ∀ᶠ N : ℕ in atTop,
      ∃ Ω : Set (SphericalModel.Disorder N (μ.finiteCutoff P hP).maxDegree),MeasurableSet Ω ∧
        (SphericalModel.disorderLaw N (μ.finiteCutoff P hP).maxDegree).real Ωᶜ≤C*Real.exp (-a*N) ∧
        ∀ J∈Ω,∀ hN : 2≤N,
          (normalizedSphericalSpectralData hN β (fieldOfMixture (μ.finiteCutoff P hP) J)
            (fieldOfMixture_contDiff (μ.finiteCutoff P hP) J).continuous).eigenvalue
              (Nat.floor (Real.exp (κ*N)))≤Real.exp (-σ*N)) :
    ∀ᶠ n : ℕ in atTop,∃ Ω : Set (Disorder (n+1)),MeasurableSet Ω ∧
      (disorderLaw (n+1)).real Ωᶜ≤(C+2)*Real.exp (-min a b*(n+1:ℕ)) ∧
      ∀ J∈Ω,∀ hn : 1≤n,
        (infiniteSpectralData n hn β μ J).eigenvalue
          (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤Real.exp (-(σ-2*β*h)*(n+1:ℕ)) := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hfinite,eventually_ge_atTop 1] with n hfinite hn
  obtain ⟨Ωf,hΩf,hfail,hgood⟩ := hfinite
  obtain ⟨R,hR,hRm,hRg⟩ := (summableJetDisorder_ae (N := n+1) (by omega) μ).exists_measurable_mem
  let f := finiteDisorder (N := n+1) (μ.finiteCutoff P hP).maxDegree
  let T : Set (Disorder (n+1)) := {J|‖tailSphere μ (P-1) J‖≤h*(n+1:ℕ)}
  have hT : MeasurableSet T := measurableSet_le (tailSphere_measurable μ (P-1)).norm measurable_const
  have hpre : MeasurableSet (f ⁻¹' Ωf) := finiteDisorder_measurable hΩf
  refine ⟨(f ⁻¹' Ωf)∩T∩R,(hpre.inter hT).inter hRm,?_,?_⟩
  · have hnull : (disorderLaw (n+1)).real Rᶜ=0 := by
      have hh : disorderLaw (n+1) Rᶜ=0 := mem_ae_iff.mp hR
      rw [measureReal_def,hh,ENNReal.toReal_zero]
    have hp : (disorderLaw (n+1)).real (f ⁻¹' Ωf)ᶜ≤C*Real.exp (-a*(n+1:ℕ)) := by
      rw [← preimage_compl]
      change (disorderLaw (n+1)).real {J | finiteDisorder (μ.finiteCutoff P hP).maxDegree J∈Ωfᶜ}≤_
      simpa only [mem_compl_iff] using
        (finiteDisorder_hasLaw.measureReal_eq hΩf.compl).le.trans hfail
    have ht : (disorderLaw (n+1)).real Tᶜ≤2*Real.exp (-b*(n+1:ℕ)) := by
      simpa only [T,compl_setOf,not_le] using htail (n+1) (by omega)
    rw [compl_inter,compl_inter]
    have h1 := measureReal_union_le (μ := disorderLaw (n+1)) ((f ⁻¹' Ωf)ᶜ∪Tᶜ) Rᶜ
    have h2 := measureReal_union_le (μ := disorderLaw (n+1)) (f ⁻¹' Ωf)ᶜ Tᶜ
    have he (r : ℝ) (hr : min a b≤r) : Real.exp (-r*(n+1:ℕ))≤Real.exp (-min a b*(n+1:ℕ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hr) (by positivity)
    have hpa := mul_le_mul_of_nonneg_left (he a (min_le_left _ _)) hC
    have hpb := he b (min_le_right _ _)
    linarith
  · intro J hJ hn'
    have hf := hgood (f J) hJ.1.1 (by omega)
    have heq : fieldOfMixture (μ.finiteCutoff P hP) (f J)=partialField μ (P-1) J :=
      funext (finiteCutoff_field μ P hP J)
    have hf' : (partialSpectralData n hn' β μ (P-1) J).eigenvalue
        (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤Real.exp (-σ*(n+1:ℕ)) := by
      have he := spectral_eigenvalue_congr (show 2≤n+1 by omega) β _ _
        (fieldOfMixture_contDiff (μ.finiteCutoff P hP) (f J)).continuous
        (partialField_contDiff μ (P-1) J).continuous heq (Nat.floor (Real.exp (κ*(n+1:ℕ))))
      exact he ▸ hf
    have ht := infinite_eigenvalue_le_partial_of_tail_bound n hn' μ (P-1) J
      (hRg J hJ.2) hβ hJ.1.2 (Nat.floor (Real.exp (κ*(n+1:ℕ))))
    apply ht.trans
    calc
      _ ≤ Real.exp (2*β*h*(n+1:ℕ))*Real.exp (-σ*(n+1:ℕ)) :=
        mul_le_mul_of_nonneg_left hf' (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add];congr 1;ring

end SlowEquilibration.SphericalInfiniteModel
