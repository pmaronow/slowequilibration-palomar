module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

@[expose] public section

/-! Actual twice-differentiable quadratic perturbations of probability
integrals. These are the analytic derivatives used in the Prékopa proof
of posterior variance bounds; no variance inequality is assumed. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace QuantitativeFollowup

def quadraticTiltWeight {Ω : Type*} (f g : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  Real.exp (t*f x-t^2*g x/2)

def quadraticTiltSlope {Ω : Type*} (f g : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  (f x-t*g x)*quadraticTiltWeight f g t x

def quadraticTiltCurvature {Ω : Type*} (f g : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  ((f x-t*g x)^2-g x)*quadraticTiltWeight f g t x

theorem hasDerivAt_quadraticTiltWeight {Ω : Type*} (f g : Ω → ℝ) (x : Ω) (t : ℝ) :
    HasDerivAt (fun t => quadraticTiltWeight f g t x) (quadraticTiltSlope f g t x) t := by
  have hd := ((hasDerivAt_id t).mul_const (f x)).sub
    ((((hasDerivAt_id t).pow 2).mul_const (g x)).div_const 2)
  convert hd.exp using 1 <;> simp only [quadraticTiltWeight,quadraticTiltSlope,id_eq,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Nat.cast_ofNat,pow_one,one_mul] <;> ring

theorem hasDerivAt_quadraticTiltSlope {Ω : Type*} (f g : Ω → ℝ) (x : Ω) (t : ℝ) :
    HasDerivAt (fun t => quadraticTiltSlope f g t x) (quadraticTiltCurvature f g t x) t := by
  have hd := ((hasDerivAt_const t (f x)).sub ((hasDerivAt_id t).mul_const (g x))).mul
    (hasDerivAt_quadraticTiltWeight f g x t)
  convert hd using 1
  · rfl
  · dsimp only [quadraticTiltWeight,quadraticTiltSlope,quadraticTiltCurvature,
      Pi.sub_apply,id_eq]
    ring

theorem quadraticTiltWeight_bound {Ω : Type*} (f g : Ω → ℝ) (Kf Kg R t : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hR : 0 ≤ R)
    (hf : ∀ x, |f x| ≤ Kf) (hg : ∀ x, |g x| ≤ Kg) (ht : |t| ≤ R) (x : Ω) :
    ‖quadraticTiltWeight f g t x‖ ≤ Real.exp (R*Kf+R^2*Kg/2) := by
  rw [quadraticTiltWeight,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have htf : t*f x ≤ R*Kf :=
    (le_abs_self _).trans ((abs_mul t (f x)).le.trans
      (mul_le_mul ht (hf x) (abs_nonneg _) hR))
  have ht2 : t^2 ≤ R^2 := by nlinarith [sq_abs t,abs_nonneg t]
  have htg : -(t^2*g x/2) ≤ R^2*Kg/2 := by
    have hg' := neg_le_abs (g x)
    have hh := mul_le_mul_of_nonneg_left (hg'.trans (hg x)) (sq_nonneg t)
    have hh2 := mul_le_mul_of_nonneg_right ht2 hKg
    nlinarith
  linarith

theorem quadraticTiltSlope_bound {Ω : Type*} (f g : Ω → ℝ) (Kf Kg R t : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hR : 0 ≤ R)
    (hf : ∀ x, |f x| ≤ Kf) (hg : ∀ x, |g x| ≤ Kg) (ht : |t| ≤ R) (x : Ω) :
    ‖quadraticTiltSlope f g t x‖ ≤ (Kf+R*Kg)*Real.exp (R*Kf+R^2*Kg/2) := by
  have hlin : |f x-t*g x| ≤ Kf+R*Kg := by
    calc
      _ ≤ |f x| + |t*g x| := abs_sub _ _
      _ = |f x| + |t| * |g x| := by rw [abs_mul]
      _ ≤ _ := add_le_add (hf x) (mul_le_mul ht (hg x) (abs_nonneg _) hR)
  rw [quadraticTiltSlope,norm_mul,Real.norm_eq_abs (f x-t*g x)]
  exact mul_le_mul hlin (quadraticTiltWeight_bound f g Kf Kg R t hKf hKg hR hf hg ht x)
    (norm_nonneg _) (by positivity)

theorem quadraticTiltCurvature_bound {Ω : Type*} (f g : Ω → ℝ) (Kf Kg R t : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hR : 0 ≤ R)
    (hf : ∀ x, |f x| ≤ Kf) (hg : ∀ x, |g x| ≤ Kg) (ht : |t| ≤ R) (x : Ω) :
    ‖quadraticTiltCurvature f g t x‖ ≤
      ((Kf+R*Kg)^2+Kg)*Real.exp (R*Kf+R^2*Kg/2) := by
  have hlin : |f x-t*g x| ≤ Kf+R*Kg := by
    calc
      _ ≤ |f x| + |t*g x| := abs_sub _ _
      _ = |f x| + |t| * |g x| := by rw [abs_mul]
      _ ≤ _ := add_le_add (hf x) (mul_le_mul ht (hg x) (abs_nonneg _) hR)
  have hs : |(f x-t*g x)^2-g x| ≤ (Kf+R*Kg)^2+Kg := by
    have hss : (f x-t*g x)^2 ≤ (Kf+R*Kg)^2 := by
      nlinarith [sq_abs (f x-t*g x),abs_nonneg (f x-t*g x)]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact add_le_add hss (hg x))
  rw [quadraticTiltCurvature,norm_mul,Real.norm_eq_abs ((f x-t*g x)^2-g x)]
  exact mul_le_mul hs (quadraticTiltWeight_bound f g Kf Kg R t hKf hKg hR hf hg ht x)
    (norm_nonneg _) (by positivity)

end QuantitativeFollowup
