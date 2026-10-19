module

public import SphericalAging.HamiltonianCoefficientBounds
public import SphericalAging.SecantCoefficient
public import Mathlib.MeasureTheory.Function.L2Space

public section

/-! Differentiation of actual scalar expectations along an L² state
family. This supplies the Gaussian Stein observable derivative without
requiring samplewise differentiability of the stochastic flow. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped InnerProductSpace NNReal ENNReal
namespace SphericalAging.GaussianObservableDerivative
open HardSphereDynamics
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[expose] abbrev StateL2 (N : ℕ) (P : Measure Ω) := Lp (State N) 2 P

@[expose] def observable (g : State N → ℝ) (U : StateL2 N P) : ℝ := ∫ ω,g (U ω) ∂P

theorem observable_integrable (g : State N → ℝ) (hg : Continuous g) (C : ℝ≥0)
    (hC : ∀ x,‖g x‖ ≤ C) (U : StateL2 N P) : Integrable (fun ω => g (U ω)) P := by
  exact (MemLp.of_bound (hg.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) C
    (.of_forall (fun ω => hC (U ω))) : MemLp (fun ω => g (U ω)) 2 P).integrable (by norm_num)

theorem gradient_memLp (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ≥0)
    (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K) (U : StateL2 N P) :
    MemLp (fun ω => gradient g (U ω)) 2 P := by
  have hc : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (State N)).symm.continuous.comp (hg.continuous_fderiv (by simp))
  apply MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)) K
  exact .of_forall (fun ω => by simpa only [gradient,LinearIsometryEquiv.norm_map] using hK (U ω))

@[expose] def gradientClass (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ≥0)
    (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K) (U : StateL2 N P) : StateL2 N P :=
  (gradient_memLp g hg K hK U).toLp (fun ω => gradient g (U ω))

@[expose] def observableDerivative (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ≥0)
    (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K) (U : StateL2 N P) : StateL2 N P →L[ℝ] ℝ :=
  innerSL ℝ (gradientClass g hg K hK U)

theorem observableDerivative_apply (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ≥0)
    (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K) (U V : StateL2 N P) :
    observableDerivative g hg K hK U V = ∫ ω,fderiv ℝ g (U ω) (V ω) ∂P := by
  change inner ℝ (gradientClass g hg K hK U) V = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(gradient_memLp g hg K hK U).coeFn_toLp] with ω hω
  rw [show gradientClass g hg K hK U ω=gradient g (U ω) from hω]
  exact inner_gradient_left

theorem observable_remainder_bound (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (C K L : ℝ≥0) (hC : ∀ x,‖g x‖ ≤ C) (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K)
    (hL : LipschitzWith L (fderiv ℝ g)) (U V : StateL2 N P) :
    ‖observable g V-observable g U-observableDerivative g hg K hK U (V-U)‖ ≤
      (L : ℝ)*‖V-U‖^2 := by
  let G := gradientClass g hg K hK U
  have hsq : Integrable (fun ω => ‖(V-U) ω‖^2) P := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.integrable_inner (𝕜 := ℝ) (V-U) (V-U))
  have hi := L2.integrable_inner (𝕜 := ℝ) G (V-U)
  have hc : (fun ω => inner ℝ (G ω) ((V-U) ω)) =ᵐ[P]
      (fun ω => fderiv ℝ g (U ω) (V ω-U ω)) := by
    filter_upwards [(gradient_memLp g hg K hK U).coeFn_toLp,Lp.coeFn_sub V U] with ω hω hs
    change inner ℝ (gradientClass g hg K hK U ω) ((V-U) ω) = _
    rw [show gradientClass g hg K hK U ω=gradient g (U ω) from hω,hs]
    exact inner_gradient_left
  have hd := hi.congr hc
  have hrem : Integrable (fun ω => g (V ω)-g (U ω)-fderiv ℝ g (U ω) (V ω-U ω)) P :=
    ((observable_integrable g hg.continuous C hC V).sub
      (observable_integrable g hg.continuous C hC U)).sub hd
  have he : observable g V-observable g U-observableDerivative g hg K hK U (V-U) =
      ∫ ω,g (V ω)-g (U ω)-fderiv ℝ g (U ω) (V ω-U ω) ∂P := by
    unfold observable observableDerivative
    change (∫ ω,g (V ω) ∂P)-(∫ ω,g (U ω) ∂P)-inner ℝ G (V-U) = _
    rw [L2.inner_def,integral_congr_ae hc]
    rw [integral_sub,integral_sub]
    · exact observable_integrable g hg.continuous C hC V
    · exact observable_integrable g hg.continuous C hC U
    · exact (observable_integrable g hg.continuous C hC V).sub
        (observable_integrable g hg.continuous C hC U)
    · exact hd
  rw [he]
  calc
    _ ≤ ∫ ω,‖g (V ω)-g (U ω)-fderiv ℝ g (U ω) (V ω-U ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω,(L : ℝ)*‖(V-U) ω‖^2 ∂P := by
      apply integral_mono_ae hrem.norm (hsq.const_mul _)
      filter_upwards [Lp.coeFn_sub V U] with ω hω
      rw [hω]
      exact SecantCoefficient.taylor_remainder_bound hg hL (U ω) (V ω)
    _ = (L : ℝ)*‖V-U‖^2 := by
      rw [integral_const_mul]
      congr 1
      simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) (V-U) (V-U)).symm

/-- The actual expectation functional is Fréchet differentiable on L². -/
theorem observable_hasFDerivAt (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (C K L : ℝ≥0) (hC : ∀ x,‖g x‖ ≤ C) (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K)
    (hL : LipschitzWith L (fderiv ℝ g)) (U : StateL2 N P) :
    HasFDerivAt (observable g) (observableDerivative g hg K hK U) U := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro ε hε
  have hd : 0 < ε/((L : ℝ)+1) := div_pos hε (by positivity)
  have hev : ∀ᶠ V : StateL2 N P in 𝓝 0,‖V‖ < ε/((L : ℝ)+1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : StateL2 N P) hd] with V hV
    simpa only [Metric.mem_ball,dist_zero_right] using hV
  filter_upwards [hev] with V hV
  have hh := observable_remainder_bound g hg C K L hC hK hL U (U+V)
  simp only [add_sub_cancel_left] at hh
  refine hh.trans ?_
  have hLv : (L : ℝ)*‖V‖ ≤ ε := by
    have hh := (lt_div_iff₀ (show 0 < (L : ℝ)+1 by positivity)).mp hV
    nlinarith [norm_nonneg V]
  nlinarith [mul_le_mul_of_nonneg_right hLv (norm_nonneg V)]

/-- Genuine L² differentiability of a state family gives the scalar
observable derivative; no samplewise parameter derivative is required. -/
theorem observable_family_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : State N → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (C K L : ℝ≥0)
    (hC : ∀ x,‖g x‖ ≤ C) (hK : ∀ x,‖fderiv ℝ g x‖ ≤ K)
    (hL : LipschitzWith L (fderiv ℝ g)) {X : E → StateL2 N P} {D : E →L[ℝ] StateL2 N P}
    {x : E} (hX : HasFDerivAt X D x) :
    HasFDerivAt (fun y => ∫ ω,g (X y ω) ∂P)
      ((observableDerivative g hg K hK (X x)).comp D) x :=
  (observable_hasFDerivAt g hg C K L hC hK hL (X x)).comp x hX

end SphericalAging.GaussianObservableDerivative
