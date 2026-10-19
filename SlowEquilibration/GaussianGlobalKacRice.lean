-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianLocalCoordinates
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Global Euclidean full-coefficient marked Gaussian Kac--Rice

A countable open cover is constructed from actual observation surjectivity.
Its disjoint Borel partition glues the independently proved canonical local
formula, preserving arbitrary full-coefficient Borel marks and infinite sums.
-/

@[expose] public section

namespace SlowEquilibration.GaussianLocalCoordinates

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianRegression
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]

/-- Gaussian-a.e. measurability of the true zero count in a constructed local
coefficient domain, obtained from the genuine incidence area theorem. -/
theorem local_zeroCount_aemeasurable
    (Gamma : U → E →L[ℝ] U) (u0 : U) (hA : Surjective (Gamma u0))
    (s : Set U) (hs : IsOpen s) (hG : ContDiffOn ℝ 1 Gamma s)
    (hblock : ∀ u ∈ s, (firstBlock Gamma u0 hA u).IsInvertible)
    (psi : E → U → ℝ≥0∞) (hpsi : Measurable fun p : E × U => psi p.1 p.2) :
    AEMeasurable (zeroCount Gamma s psi) (stdGaussian E) := by
  let j := coefficientSplit (Gamma u0) hA
  let G1 := firstBlock Gamma u0 hA
  let G2 := secondBlock Gamma u0
  let phi : (U × (Gamma u0).ker) → U → ℝ≥0∞ :=
    fun z u => psi (j (WithLp.toLp 2 z)) u
  have hm : Measurable fun p : (U × (Gamma u0).ker) × U => phi p.1 p.2 := by
    exact hpsi.comp ((j.continuous.measurable.comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ U (Gamma u0).ker).symm.continuous.measurable).comp
        measurable_fst |>.prodMk measurable_snd)
  have h1 := firstBlock_contDiffOn Gamma u0 hA s hG
  have h2 := secondBlock_contDiffOn Gamma u0 s hG
  have hcount : AEMeasurable (CoefficientKacRice.gradientCount G1 G2 s phi)
      (GaussianKacRice.splitGaussian (U := U) (V := (Gamma u0).ker)) := by
    have h := CoefficientKacRice.graphCount_aemeasurable
      ((volume : Measure U).prod (volume : Measure (Gamma u0).ker))
      (CoefficientKacRice.alpha G1 G2) s hs
      (CoefficientKacRice.alpha_contDiffOn G1 G2 s hs h1 h2 hblock) phi hm
    have he := funext fun z => CoefficientKacRice.gradientCount_eq_graphCount G1 G2 s hblock phi z
    rw [← he] at h
    rw [GaussianKacRice.splitGaussian_density]
    exact h.mono_ac (withDensity_absolutelyContinuous _ _)
  have hgrad (z : WithLp 2 (U × (Gamma u0).ker)) :
      CoefficientKacRice.gradient G1 G2 z.ofLp = fun u => Gamma u (j z) := by
    funext u
    exact congrArg (fun T : WithLp 2 (U × (Gamma u0).ker) →L[ℝ] U => T z)
      (observationAt_eq_comp_split Gamma u0 hA u)
  have hc (z : WithLp 2 (U × (Gamma u0).ker)) :
      CoefficientKacRice.gradientCount G1 G2 s phi z.ofLp = zeroCount Gamma s psi (j z) := by
    unfold CoefficientKacRice.gradientCount zeroCount
    rw [hgrad]
  have h0 : AEMeasurable (fun z : WithLp 2 (U × (Gamma u0).ker) => zeroCount Gamma s psi (j z))
      (stdGaussian (WithLp 2 (U × (Gamma u0).ker))) := by
    have h := hcount.comp_aemeasurable'
      (WithLp.prodContinuousLinearEquiv 2 ℝ U (Gamma u0).ker).continuous.measurable.aemeasurable
    simpa only [hc] using h
  have hj : (stdGaussian E).map j.symm = stdGaussian (WithLp 2 (U × (Gamma u0).ker)) := stdGaussian_map j.symm
  rw [← hj] at h0
  have h := h0.comp_aemeasurable' j.symm.continuous.measurable.aemeasurable
  simpa only [j.apply_symm_apply] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
/-- True zero counts localized by a spatial Borel indicator retain the
complete count on that piece, with no finite-count surrogate. -/
lemma zeroCount_indicator (Gamma : U → E →L[ℝ] U) (s p : Set U) (hp : p ⊆ s)
    (psi : E → U → ℝ≥0∞) (z : E) :
    zeroCount Gamma s (fun z => p.indicator (psi z)) z = zeroCount Gamma p psi z := by
  classical
  unfold zeroCount
  rw [tsum_subtype, tsum_subtype]
  apply tsum_congr
  intro u
  by_cases hup : u ∈ p
  · have hus := hp hup
    simp [Set.indicator, hup, hus]
  · simp [Set.indicator, hup]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace U] [BorelSpace U] in
/-- Every C1 surjective observation field admits a countable cover by actual
invertible coefficient-block neighborhoods. -/
theorem countable_invertible_block_cover
    (Gamma : U → E →L[ℝ] U) (s : Set U) (hs : IsOpen s) (hG : ContDiffOn ℝ 1 Gamma s)
    (hne : s.Nonempty) (hSurj : ∀ u ∈ s, Surjective (Gamma u)) :
    ∃ a : ℕ → s, ∃ v : ℕ → Set U,
      (∀ n, IsOpen (v n)) ∧ (∀ n, v n ⊆ s) ∧ (⋃ n, v n) = s ∧
      ∀ n u, u ∈ v n → (firstBlock Gamma (a n) (hSurj (a n) (a n).2) u).IsInvertible := by
  classical
  choose V hVo hva hVs hVi using (fun a : s =>
    exists_invertible_block_neighborhood Gamma s hs hG a a.2 (hSurj a a.2))
  have hcover : (⋃ a : s, V a) = s := by
    ext u
    constructor
    · intro hu
      obtain ⟨a, hu⟩ := mem_iUnion.mp hu
      exact hVs a hu
    · intro hu
      exact mem_iUnion.mpr ⟨⟨u, hu⟩, hva ⟨u, hu⟩⟩
  obtain ⟨T, hT, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hTne : T.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    have hx : u ∈ ⋃ a ∈ T, V a := by rw [hTu, hcover]; exact hu
    obtain ⟨a, ha, _⟩ := mem_iUnion₂.mp hx
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hT.exists_eq_range hTne
  refine ⟨a, fun n => V (a n), fun n => hVo (a n), fun n => hVs (a n), ?_, ?_⟩
  · rw [← biUnion_range, ← ha, hTu, hcover]
  · exact fun n u hu => hVi (a n) u hu

/-- Global Euclidean marked Kac--Rice for the actual arbitrary finite
Gaussian coefficient field and every nonnegative full-coefficient Borel mark.
Surjectivity constructs the local blocks and countable partition internally. -/
theorem marked_kacRice
    (Gamma : U → E →L[ℝ] U) (s : Set U) (hs : IsOpen s) (hG : ContDiffOn ℝ 1 Gamma s)
    (hSurj : ∀ u ∈ s, Surjective (Gamma u))
    (psi : E → U → ℝ≥0∞) (hpsi : Measurable fun p : E × U => psi p.1 p.2) :
    AEMeasurable (zeroCount Gamma s psi) (stdGaussian E) ∧
    (∫⁻ z, zeroCount Gamma s psi z ∂stdGaussian E) =
      ∫⁻ u in s, observationPdf (Gamma u) 0 *
        ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
          ∂regressionKernel (Gamma u) 0 := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨a, v, hvOpen, hvSub, hvUnion, hvBlock⟩ :=
      countable_invertible_block_cover Gamma s hs hG hne hSurj
    let p := disjointed v
    have hpMeas : ∀ n, MeasurableSet (p n) := MeasurableSet.disjointed (fun n => (hvOpen n).measurableSet)
    have hpDisj : Pairwise (fun i j => Disjoint (p i) (p j)) := disjoint_disjointed v
    have hpUnion : (⋃ n, p n) = s := by rw [iUnion_disjointed, hvUnion]
    have hpSub : ∀ n, p n ⊆ v n := disjointed_subset v
    let psiN : ℕ → E → U → ℝ≥0∞ := fun n z => (p n).indicator (psi z)
    have hpsiN : ∀ n, Measurable fun q : E × U => psiN n q.1 q.2 := by
      intro n
      change Measurable ((Prod.snd ⁻¹' p n).indicator (fun q : E × U => psi q.1 q.2))
      exact hpsi.indicator ((hpMeas n).preimage measurable_snd)
    have hcount (z : E) : zeroCount Gamma s psi z = ∑' n, zeroCount Gamma (v n) (psiN n) z := by
      calc
        _ = ∑' n, zeroCount Gamma (p n) psi z :=
          WeightedAreaFormula.fiberSum_partition (fun u => Gamma u z) s (psi z) p hpDisj hpUnion 0
        _ = _ := by
          apply tsum_congr
          intro n
          exact (zeroCount_indicator Gamma (v n) (p n) (hpSub n) psi z).symm
    have hAE : ∀ n, AEMeasurable (zeroCount Gamma (v n) (psiN n)) (stdGaussian E) := by
      intro n
      exact local_zeroCount_aemeasurable Gamma (a n) (hSurj (a n) (a n).2)
        (v n) (hvOpen n) (hG.mono (hvSub n)) (hvBlock n) (psiN n) (hpsiN n)
    refine ⟨?_, ?_⟩
    · have he := funext hcount
      rw [he]
      exact AEMeasurable.tsum hAE
    · simp_rw [hcount]
      rw [lintegral_tsum hAE]
      calc
        (∑' n, ∫⁻ z, zeroCount Gamma (v n) (psiN n) z ∂stdGaussian E) =
            ∑' n, ∫⁻ u in p n, observationPdf (Gamma u) 0 *
              ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
                ∂regressionKernel (Gamma u) 0 := by
          apply tsum_congr
          intro n
          rw [local_whole_coefficients_kacRice Gamma (a n) (hSurj (a n) (a n).2)
            (v n) (hvOpen n) (hG.mono (hvSub n)) (hvBlock n) (psiN n) (hpsiN n)]
          have he : (fun u => observationPdf (Gamma u) 0 *
              ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psiN n z u
                ∂regressionKernel (Gamma u) 0) =
              (p n).indicator (fun u => observationPdf (Gamma u) 0 *
                ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
                  ∂regressionKernel (Gamma u) 0) := by
            funext u
            by_cases hu : u ∈ p n
            · simp [psiN, hu]
            · simp [psiN, hu]
          rw [he, setLIntegral_indicator (hpMeas n), inter_eq_left.mpr (hpSub n)]
        _ = _ := by
          rw [← hpUnion]
          exact (lintegral_iUnion hpMeas hpDisj _).symm
  · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [hs0]
    have he : zeroCount Gamma ∅ psi = 0 := by
      funext z
      unfold zeroCount
      simp
    rw [he]
    exact ⟨measurable_const.aemeasurable, by simp⟩

end
end SlowEquilibration.GaussianLocalCoordinates
