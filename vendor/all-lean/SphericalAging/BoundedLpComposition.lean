module

public import SphericalAging.LpQuadraticRemainder
public import SphericalAging.LpClassMomentAlgebra

public section

/-! Bounded uniformly continuous functions act continuously on vector L²
over a probability law. No samplewise convergence premise is required. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.BoundedLpComposition
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Ω E G : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedAddCommGroup G] {P : Measure Ω} [IsProbabilityMeasure P]

theorem difference_small_plus_linear (g : E → G) (huc : UniformContinuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) :
    ∀ ε : ℝ,0<ε → ∃ C : ℝ,0≤C ∧ ∀ x y,
      ‖g y-g x‖≤ε+C*‖y-x‖ := by
  intro ε hε
  obtain ⟨δ,hδ,hm⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨2*(K : ℝ)/δ,by positivity,?_⟩
  intro x y
  by_cases hxy : ‖y-x‖<δ
  · have hs := hm (show dist y x<δ by simpa only [dist_eq_norm] using hxy)
    change dist (g y) (g x)<ε at hs
    rw [dist_eq_norm] at hs
    exact hs.le.trans (le_add_of_nonneg_right (by positivity))
  · have hfar : δ≤‖y-x‖ := le_of_not_gt hxy
    have hb := (norm_sub_le (g y) (g x)).trans (add_le_add (hK y) (hK x))
    have hh : 2*(K : ℝ)≤(2*(K : ℝ)/δ)*‖y-x‖ := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hδ).mpr
      exact mul_le_mul_of_nonneg_left hfar (by positivity)
    linarith

theorem composition_memLp (g : E → G) (hg : Continuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (U : Lp E 2 P) :
    MemLp (fun ω => g (U ω)) 2 P :=
  MemLp.of_bound (hg.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) K
    (.of_forall (fun ω => hK (U ω)))

@[expose] def composition (g : E → G) (hg : Continuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (U : Lp E 2 P) : Lp G 2 P :=
  (composition_memLp g hg K hK U).toLp _

theorem composition_coeFn (g : E → G) (hg : Continuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (U : Lp E 2 P) :
    composition g hg K hK U=ᵐ[P] fun ω => g (U ω) :=
  (composition_memLp g hg K hK U).coeFn_toLp

theorem lpNorm_le_const_add_norm {W : Ω → G} {U : Ω → E}
    (hW : MemLp W 2 P) (hU : MemLp U 2 P) {ε C : ℝ} (hε : 0≤ε) (hC : 0≤C)
    (hb : ∀ᵐ ω ∂P,‖W ω‖≤ε+C*‖U ω‖) :
    lpNorm W 2 P≤ε+C*lpNorm U 2 P := by
  have hB : MemLp (fun ω => ε+C*‖U ω‖) 2 P := (memLp_const ε).add (hU.norm.const_mul C)
  have he := eLpNorm_mono_ae_real (p := 2) hW.aestronglyMeasurable hb
  have hn : lpNorm W 2 P≤lpNorm (fun ω => ε+C*‖U ω‖) 2 P := by
    simpa only [toReal_eLpNorm] using
      (ENNReal.toReal_le_toReal hW.eLpNorm_ne_top hB.eLpNorm_ne_top).mpr he
  apply hn.trans
  have ht := lpNorm_add_le (memLp_const (μ := P) (p := 2) ε)
    (by norm_num : (1 : ℝ≥0∞)≤2) (g := fun ω => C*‖U ω‖)
  change lpNorm ((fun _ : Ω => ε)+(fun ω => C*‖U ω‖)) 2 P≤_
  simpa [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hε,abs_of_nonneg hC,
    LpMultiplierTruncation.lpNorm_norm hU,lpNorm_const'] using ht

/-- Genuine L² continuity of composition by any bounded uniformly
continuous function. -/
theorem composition_continuous (g : E → G) (huc : UniformContinuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) :
    Continuous (composition (P := P) g huc.continuous K hK) := by
  apply continuous_iff_continuousAt.mpr
  intro U
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨C,hC,hb⟩ := difference_small_plus_linear g huc K hK (ε/2) (by positivity)
  refine ⟨ε/(2*(C+1)),by positivity,?_⟩
  intro V hV
  let A := composition (P := P) g huc.continuous K hK
  have hsum := lpNorm_le_const_add_norm (Lp.memLp (A V-A U)) (Lp.memLp (V-U))
    (show 0≤ε/2 by positivity) hC ?_
  · have hn := hsum
    simp only [LpClassMomentAlgebra.lpNorm_two_coe] at hn
    change ‖A V-A U‖≤ε/2+C*‖V-U‖ at hn
    rw [dist_eq_norm] at hV ⊢
    have hv := (lt_div_iff₀ (show (0 : ℝ)<2*(C+1) by positivity)).mp hV
    nlinarith [norm_nonneg (V-U)]
  · filter_upwards [composition_coeFn g huc.continuous K hK V,
      composition_coeFn g huc.continuous K hK U,Lp.coeFn_sub (A V) (A U),Lp.coeFn_sub V U]
      with ω hv hu ha hdiff
    change ‖(A V-A U) ω‖≤_
    simp only [Pi.sub_apply] at ha hdiff
    rw [ha,hdiff]
    change ‖composition g huc.continuous K hK V ω-
      composition g huc.continuous K hK U ω‖≤_
    rw [hv,hu]
    exact hb (U ω) (V ω)

end SphericalAging.BoundedLpComposition
