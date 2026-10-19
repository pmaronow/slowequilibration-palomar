module
public import QuantitativeFollowup.QuadraticTiltVariance
public import QuantitativeFollowup.LogConcaveMarginal
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! A genuine Prékopa variance bound for actual densities. The geometric
input is joint convexity of a displayed quadratic perturbation of the
potential. It is not an assumed variance, integration-by-parts, or Poisson
identity. To obtain inverse-Hessian Brascamp--Lieb one must still prove
this convexity for the inverse-Hessian correction plus an arbitrarily
small positive constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace QuantitativeFollowup

def posteriorDensityMeasure {E : Type*} [MeasureSpace E]
    (V : E → ℝ) : Measure E :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))

def quadraticPosteriorPotential {E : Type*} (V f g : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  V x-t*f x+t^2*g x/2

theorem posterior_quadratic_weight_eq {E : Type*} (V f g : E → ℝ) (t : ℝ) :
    (fun x => (ENNReal.ofReal (Real.exp (-V x))).toReal • quadraticTiltWeight f g t x) =
      (fun x => Real.exp (-quadraticPosteriorPotential V f g t x)) := by
  funext x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,quadraticTiltWeight,←Real.exp_add]
  congr 1
  unfold quadraticPosteriorPotential
  ring

theorem integral_posterior_quadraticTilt {E : Type*} [MeasureSpace E]
    (V f g : E → ℝ) (hV : Measurable V) (t : ℝ) :
    (∫ x, quadraticTiltWeight f g t x ∂posteriorDensityMeasure V) =
      ∫ x, Real.exp (-quadraticPosteriorPotential V f g t x) := by
  rw [posteriorDensityMeasure,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (.of_forall fun x => ENNReal.ofReal_lt_top),posterior_quadratic_weight_eq]

theorem posterior_variance_le_of_joint_convex_quadraticTilt {d : ℕ}
    (V f g : (Fin (d+1) → ℝ) → ℝ)
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : Measurable V) (hf : Measurable f) (hg : Measurable g)
    (Kf Kg : ℝ) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hfb : ∀ x, |f x| ≤ Kf) (hgb : ∀ x, |g x| ≤ Kg)
    (ε : ℝ) (hε : 0 < ε)
    (hW : ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Fin (d+1) → ℝ)))
      (Function.uncurry (quadraticPosteriorPotential V f g))) :
    variance f (posteriorDensityMeasure V) ≤ ∫ x, g x ∂posteriorDensityMeasure V := by
  have hI (t : ℝ) : Integrable (fun x => Real.exp (-quadraticPosteriorPotential V f g t x)) := by
    have hi := integrable_quadraticTiltWeight (posteriorDensityMeasure V)
      f g hf hg Kf Kg hKf hKg hfb hgb t
    rw [posteriorDensityMeasure,integrable_withDensity_iff_integrable_smul'
      (by fun_prop : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x))))
      (.of_forall fun x => ENNReal.ofReal_lt_top),posterior_quadratic_weight_eq] at hi
    exact hi
  have hc := concaveOn_log_integral_exp_neg (Ioo (-ε) ε) (convex_Ioo _ _)
    (quadraticPosteriorPotential V f g) hW
    (fun t _ht => by unfold quadraticPosteriorPotential; fun_prop) (fun t _ht => hI t)
  apply variance_le_of_concave_quadraticTilt (posteriorDensityMeasure V)
    f g hf hg Kf Kg hKf hKg hfb hgb ε hε
  convert hc using 1
  funext t
  rw [integral_posterior_quadraticTilt V f g hV]

end QuantitativeFollowup
