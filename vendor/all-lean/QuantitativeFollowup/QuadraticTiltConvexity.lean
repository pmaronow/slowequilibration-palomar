module
public import QuantitativeFollowup.DirectionalConvexity
public import QuantitativeFollowup.PosteriorVariance

@[expose] public section

/-! A quantitative local convexity theorem for a displayed quadratic
posterior perturbation. All derivatives here are actual Fréchet
derivatives. The hypotheses are differential bounds and a strict
Schur-complement bound, not the desired variance inequality. -/
noncomputable section
open Set
namespace QuantitativeFollowup

def quadraticTiltLineDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V f g : E → ℝ) (t : ℝ) (x : E) (τ : ℝ) (z : E) (r : ℝ) : ℝ :=
  fderiv ℝ V (x+r • z) z-τ*f (x+r • z)-(t+r*τ)*fderiv ℝ f (x+r • z) z+
    (t+r*τ)*τ*g (x+r • z)+(t+r*τ)^2/2*fderiv ℝ g (x+r • z) z

def quadraticTiltLineCurvature {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V f g : E → ℝ) (t : ℝ) (x : E) (τ : ℝ) (z : E) (r : ℝ) : ℝ :=
  directionalHessian V (x+r • z) z-2*τ*fderiv ℝ f (x+r • z) z-
    (t+r*τ)*directionalHessian f (x+r • z) z+τ^2*g (x+r • z)+
    2*(t+r*τ)*τ*fderiv ℝ g (x+r • z) z+
    (t+r*τ)^2/2*directionalHessian g (x+r • z) z

theorem quadraticTiltLine_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V f g : E → ℝ) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (t : ℝ) (x : E) (τ : ℝ) (z : E) (r : ℝ) :
    HasDerivAt (fun s => quadraticPosteriorPotential V f g (t+s*τ) (x+s • z))
      (quadraticTiltLineDerivative V f g t x τ z r) r := by
  have ht : HasDerivAt (fun s : ℝ => t+s*τ) τ r := by
    simpa using ((hasDerivAt_id r).mul_const τ).const_add t
  have hv := hasDerivAt_on_affine_line V hV x z r
  have hfl := hasDerivAt_on_affine_line f hf x z r
  have hgl := hasDerivAt_on_affine_line g hg x z r
  convert (hv.sub (ht.mul hfl)).add (((ht.pow 2).mul hgl).div_const 2) using 1
  · rfl
  · unfold quadraticTiltLineDerivative
    simp only [Pi.pow_apply]
    ring

theorem quadraticTiltLineDerivative_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V f g : E → ℝ) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (t : ℝ) (x : E) (τ : ℝ) (z : E) (r : ℝ) :
    HasDerivAt (quadraticTiltLineDerivative V f g t x τ z)
      (quadraticTiltLineCurvature V f g t x τ z r) r := by
  have ht : HasDerivAt (fun s : ℝ => t+s*τ) τ r := by
    simpa using ((hasDerivAt_id r).mul_const τ).const_add t
  have hv := hasDerivAt_directional_on_affine_line V hV x z r
  have hfl := hasDerivAt_on_affine_line f hf x z r
  have hdf := hasDerivAt_directional_on_affine_line f hf x z r
  have hgl := hasDerivAt_on_affine_line g hg x z r
  have hdg := hasDerivAt_directional_on_affine_line g hg x z r
  convert (((hv.sub (hfl.const_mul τ)).sub (ht.mul hdf)).add
    ((ht.mul_const τ).mul hgl)).add (((ht.pow 2).div_const 2).mul hdg) using 1
  · rfl
  · unfold quadraticTiltLineCurvature
    simp only [Pi.pow_apply]
    ring

theorem quadraticTilt_curvature_nonneg {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V f g : E → ℝ) (m Kf Kg₁ Kg₂ ε t τ : ℝ) (x z : E)
    (hm : 0 ≤ m) (hKf : 0 ≤ Kf) (hKg₁ : 0 ≤ Kg₁) (hKg₂ : 0 ≤ Kg₂)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (ht : |t| ≤ ε)
    (hsmall : ε*(Kf+Kg₁+Kg₂) ≤ m)
    (hbase : m*(‖z‖^2+τ^2) ≤ directionalHessian V x z-
      2*τ*fderiv ℝ f x z+τ^2*g x)
    (hf : |directionalHessian f x z| ≤ Kf*‖z‖^2)
    (hg₁ : |fderiv ℝ g x z| ≤ Kg₁*‖z‖)
    (hg₂ : |directionalHessian g x z| ≤ Kg₂*‖z‖^2) :
    0 ≤ directionalHessian V x z-2*τ*fderiv ℝ f x z-
      t*directionalHessian f x z+τ^2*g x+
      2*t*τ*fderiv ℝ g x z+t^2/2*directionalHessian g x z := by
  have he : |t| ≤ 1 := ht.trans hε₁
  have ht₂ : t^2 ≤ ε := by nlinarith [sq_abs t,abs_nonneg t]
  have hf' := abs_le.mp hf
  have hg₁' := abs_le.mp hg₁
  have hg₂' := abs_le.mp hg₂
  have hprod₁ : |t*directionalHessian f x z| ≤ ε*Kf*‖z‖^2 := by
    rw [abs_mul]
    calc
      |t| * |directionalHessian f x z| ≤ ε*(Kf*‖z‖^2) :=
        mul_le_mul ht hf (abs_nonneg _) hε
      _ = ε*Kf*‖z‖^2 := by ring
  have hprod₂ : |2*t*τ*fderiv ℝ g x z| ≤ ε*Kg₁*(τ^2+‖z‖^2) := by
    have hyoung : 2*|τ| * ‖z‖ ≤ τ^2+‖z‖^2 := by
      nlinarith [sq_nonneg (|τ|-‖z‖),sq_abs τ]
    have hh : |2*t*τ*fderiv ℝ g x z| ≤ 2*ε*|τ| * (Kg₁*‖z‖) := by
      simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      gcongr
    calc
      _ ≤ 2*ε*|τ| * (Kg₁*‖z‖) := hh
      _ = ε*Kg₁*(2*|τ| * ‖z‖) := by ring
      _ ≤ ε*Kg₁*(τ^2+‖z‖^2) := mul_le_mul_of_nonneg_left hyoung (by positivity)
  have hprod₃ : |t^2/2*directionalHessian g x z| ≤ ε*Kg₂*‖z‖^2 := by
    have ht₂' : |t^2/2| ≤ ε := by rw [abs_of_nonneg (by positivity)]; linarith
    rw [abs_mul]
    calc
      |t^2/2| * |directionalHessian g x z| ≤ ε*(Kg₂*‖z‖^2) :=
        mul_le_mul ht₂' hg₂ (abs_nonneg _) hε
      _ = ε*Kg₂*‖z‖^2 := by ring
  have hp₁ := abs_le.mp hprod₁
  have hp₂ := abs_le.mp hprod₂
  have hp₃ := abs_le.mp hprod₃
  have hs := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ ‖z‖^2+τ^2)
  have hp : 0 ≤ ε*(Kf+Kg₂)*τ^2 := by positivity
  nlinarith

theorem convexOn_quadraticTilt_of_hessian_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V f g : E → ℝ) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (m Kf Kg₁ Kg₂ ε : ℝ)
    (hm : 0 ≤ m) (hKf : 0 ≤ Kf) (hKg₁ : 0 ≤ Kg₁) (hKg₂ : 0 ≤ Kg₂)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hsmall : ε*(Kf+Kg₁+Kg₂) ≤ m)
    (hbase : ∀ x z τ, m*(‖z‖^2+τ^2) ≤ directionalHessian V x z-
      2*τ*fderiv ℝ f x z+τ^2*g x)
    (hfb : ∀ x z, |directionalHessian f x z| ≤ Kf*‖z‖^2)
    (hg₁b : ∀ x z, |fderiv ℝ g x z| ≤ Kg₁*‖z‖)
    (hg₂b : ∀ x z, |directionalHessian g x z| ≤ Kg₂*‖z‖^2) :
    ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set E))
      (Function.uncurry (quadraticPosteriorPotential V f g)) := by
  let S := Ioo (-ε) ε ×ˢ (univ : Set E)
  have hS : Convex ℝ S := (convex_Ioo _ _).prod convex_univ
  apply convexOn_of_line_second_derivatives S hS _
    (by unfold quadraticPosteriorPotential; exact
      (hV.continuous.comp continuous_snd |>.sub
        (continuous_fst.mul (hf.continuous.comp continuous_snd)) |>.add
        ((continuous_fst.pow 2).mul (hg.continuous.comp continuous_snd) |>.div_const 2)).continuousOn)
  intro p hp q hq
  refine ⟨quadraticTiltLineDerivative V f g p.1 p.2 (q.1-p.1) (q.2-p.2),
    quadraticTiltLineCurvature V f g p.1 p.2 (q.1-p.1) (q.2-p.2),?_,?_,?_⟩
  · intro r hr
    simpa [Function.uncurry,Prod.smul_mk,smul_eq_mul] using
      quadraticTiltLine_hasDerivAt V f g hV hf hg p.1 p.2 (q.1-p.1) (q.2-p.2) r
  · intro r hr
    exact quadraticTiltLineDerivative_hasDerivAt V f g hV hf hg p.1 p.2
      (q.1-p.1) (q.2-p.2) r
  · intro r hr
    have hpr : p+r • (q-p) ∈ S := by
      have heq : p+r • (q-p) = (1-r) • p+r • q := by module
      rw [heq]
      exact hS hp hq (by linarith [hr.2]) hr.1.le (by ring)
    have ht : |p.1+r*(q.1-p.1)| ≤ ε := by
      exact (abs_lt.mpr hpr.1).le
    unfold quadraticTiltLineCurvature
    exact quadraticTilt_curvature_nonneg V f g m Kf Kg₁ Kg₂ ε
      (p.1+r*(q.1-p.1)) (q.1-p.1) (p.2+r • (q.2-p.2)) (q.2-p.2)
      hm hKf hKg₁ hKg₂ hε.le hε₁ ht hsmall (hbase _ _ _)
      (hfb _ _) (hg₁b _ _) (hg₂b _ _)

end QuantitativeFollowup
