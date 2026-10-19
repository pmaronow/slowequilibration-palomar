module

public import SphericalAging.BoundedLpComposition
public import SphericalAging.RandomLpCoefficient
public import SphericalAging.UniformDerivativeRemainder

public section

/-! Genuine finite-parameter differentiation of bounded C¹ observables
in L², using actual fourth-moment increments. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology ENNReal NNReal
namespace SphericalAging.BoundedLpCompositionDerivative
open HardSphereDynamics BoundedLpComposition RandomLpCoefficient LpClassMomentAlgebra
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[expose] def derivativeCoefficient (g : State N → State N) (hD : Continuous (fderiv ℝ g))
    (K : ℝ≥0) (hK : ∀ x,‖fderiv ℝ g x‖≤K) (U : Lp (State N) 2 P) :
    Coefficient (N := N) (P := P) K where
  value := fun ω => fderiv ℝ g (U ω)
  measurable := hD.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)
  bound := .of_forall (fun ω => hK (U ω))

theorem remainder_norm_le (g : State N → State N) (hg : Continuous g)
    (hD : Continuous (fderiv ℝ g)) (C K : ℝ≥0)
    (hC : ∀ x,‖g x‖≤C) (hK : ∀ x,‖fderiv ℝ g x‖≤K)
    (U V : Lp (State N) 2 P) (hUV : MemLp (V-U : Lp (State N) 2 P) 4 P)
    {ε A : ℝ} (hε : 0≤ε) (hA : 0≤A)
    (hrem : ∀ x y,‖g y-g x-fderiv ℝ g x (y-x)‖≤ε*‖y-x‖+A*‖y-x‖^2) :
    ‖composition g hg C hC V-composition g hg C hC U-
      operator (derivativeCoefficient g hD K hK U) (V-U)‖≤
        ε*‖V-U‖+A*(lpNorm (V-U : Lp (State N) 2 P) 4 P)^2 := by
  let a := derivativeCoefficient g hD K hK U
  let W := composition g hg C hC V-composition g hg C hC U-operator a (V-U)
  have hb : ∀ᵐ ω ∂P,‖W ω‖≤ε*‖(V-U : Lp (State N) 2 P) ω‖+
      A*‖(V-U : Lp (State N) 2 P) ω‖^2 := by
    filter_upwards [composition_coeFn g hg C hC V,composition_coeFn g hg C hC U,
      apply_coeFn a (V-U),Lp.coeFn_sub V U,
      Lp.coeFn_sub (composition g hg C hC V) (composition g hg C hC U),
      Lp.coeFn_sub (composition g hg C hC V-composition g hg C hC U) (operator a (V-U))]
      with ω hv hu hop hd hsub hw
    simp only [Pi.sub_apply] at hd hsub hw
    change ‖W ω‖≤_
    dsimp only [W]
    rw [hw,hsub,hv,hu,operator_apply,hop,hd]
    exact hrem (U ω) (V ω)
  have hh := LpQuadraticRemainder.lpNorm_le_small_plus_square
    (Lp.memLp (V-U)) hUV (Lp.memLp W) hε hA hb
  simpa only [lpNorm_two_coe] using hh

/-- The derivative of a finite-parameter L² observable family is proved
from its genuine L² derivative and a fourth-moment increment estimate. -/
theorem family_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : State N → State N) (hg : Differentiable ℝ g)
    (hD : UniformContinuous (fderiv ℝ g)) (C K : ℝ≥0)
    (hC : ∀ x,‖g x‖≤C) (hK : ∀ x,‖fderiv ℝ g x‖≤K)
    {X : E → Lp (State N) 2 P} {D : E →L[ℝ] Lp (State N) 2 P} {x : E}
    (hX : HasFDerivAt X D x) (B : ℝ≥0)
    (h4 : ∀ y,MemLp (X y-X x : Lp (State N) 2 P) 4 P)
    (hB : ∀ y,lpNorm (X y-X x : Lp (State N) 2 P) 4 P≤B*‖y-x‖) :
    HasFDerivAt (fun y => composition g hg.continuous C hC (X y))
      ((operator (derivativeCoefficient g hD.continuous K hK (X x))).comp D) x := by
  let a := derivativeCoefficient g hD.continuous K hK (X x)
  let A := operator a
  obtain ⟨L,hL,hbig⟩ := hX.isBigO_sub.exists_nonneg
  rw [hasFDerivAt_iff_isLittleO,isLittleO_iff]
  intro ε hε
  obtain ⟨M,hM,hm⟩ := UniformDerivativeRemainder.remainder_small_plus_quadratic g hg hD K hK
    (ε/(3*(L+1))) (by positivity)
  have hlin := (hasFDerivAt_iff_isLittleO.mp hX).bound (show 0<ε/(3*((K : ℝ)+1)) by positivity)
  have hnear : ∀ᶠ y : E in 𝓝 x,‖y-x‖<ε/(3*(M*(B : ℝ)^2+1)) := by
    filter_upwards [Metric.ball_mem_nhds x (show 0<ε/(3*(M*(B : ℝ)^2+1)) by positivity)] with y hy
    simpa only [Metric.mem_ball,dist_eq_norm] using hy
  filter_upwards [hbig.bound,hlin,hnear] with y hy hliny hneary
  have hrem := remainder_norm_le g hg.continuous hD.continuous C K hC hK
    (X x) (X y) (h4 y) (show 0≤ε/(3*(L+1)) by positivity) hM hm
  have hsplit : composition g hg.continuous C hC (X y)-composition g hg.continuous C hC (X x)-
      (A.comp D) (y-x)=
      (composition g hg.continuous C hC (X y)-composition g hg.continuous C hC (X x)-A (X y-X x))+
      A (X y-X x-D (y-x)) := by
    simp only [ContinuousLinearMap.comp_apply,map_sub]
    abel
  rw [hsplit]
  have hop : ‖A (X y-X x-D (y-x))‖≤(K : ℝ)*‖X y-X x-D (y-x)‖ :=
    norm_apply_le a _
  have hquad : M*(lpNorm (X y-X x : Lp (State N) 2 P) 4 P)^2≤M*(B : ℝ)^2*‖y-x‖^2 := by
    have hh := pow_le_pow_left₀ lpNorm_nonneg (hB y) 2
    nlinarith [mul_le_mul_of_nonneg_left hh hM]
  apply (norm_add_le _ _).trans
  apply (add_le_add hrem hop).trans
  have hl : ε/(3*(L+1))*L≤ε/3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hk : (K : ℝ)*(ε/(3*((K : ℝ)+1)))≤ε/3 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hn : M*(B : ℝ)^2*‖y-x‖≤ε/3 := by
    have hh := (lt_div_iff₀ (show 0<3*(M*(B : ℝ)^2+1) by positivity)).mp hneary
    nlinarith [norm_nonneg (y-x)]
  have hb1 := mul_le_mul_of_nonneg_left hy (show 0≤ε/(3*(L+1)) by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hliny K.coe_nonneg
  have hb3 := mul_le_mul_of_nonneg_right hl (norm_nonneg (y-x))
  have hb4 := mul_le_mul_of_nonneg_right hk (norm_nonneg (y-x))
  have hb5 := mul_le_mul_of_nonneg_right hn (norm_nonneg (y-x))
  nlinarith

end SphericalAging.BoundedLpCompositionDerivative
