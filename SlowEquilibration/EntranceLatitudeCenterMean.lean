-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeOriginalMeanEvent
public import SlowEquilibration.SphericalGaussianJet

/-! The literal source8.2 V_x is the actual center-field H_Q tangent
observable. Its true minimum-degree mean bound keeps every Q power and
the same original Gaussian-bank event, uniformly in every chosen axis. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalLatitudeTensorMoments
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem correction_uniform_constant_nonneg (p : ℕ) :
    0≤latitudeCorrectionUniformConstant p := by
  unfold latitudeCorrectionUniformConstant
  apply Finset.sum_nonneg
  intro S hS
  apply List.sum_nonneg
  intro a ha
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp ha
  positivity

/-- Center-model leading constant fixed before dimension. -/
def centerLatitudeLeadingConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  ∑ p : Degree μ.maxDegree,Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*
    (p.val.val : ℝ)*blockThreshold p

def centerLatitudeCorrectionConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  ∑ p : Degree μ.maxDegree,Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*
    latitudeCorrectionUniformConstant p.val.val

def centerLatitudeMeanConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  1+centerLatitudeLeadingConstant μ Q+centerLatitudeCorrectionConstant μ Q

/-- Exact actual Q amplitude scaling preserves the true source degree order. -/
theorem center_latitude_leading_degree_abs_le {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) (J : Disorder (n+1) μ.maxDegree) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (p : Degree μ.maxDegree)
    {r : ℝ} (hr : |r|≤1) :
    Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*
      |(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u)|≤
      (Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*(p.val.val : ℝ)*blockThreshold p)*
        Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1) := by
  rw [sqrt_centerCoefficients _ (mixtureCoefficients_nonnegative μ) hQ]
  calc
    _=(Real.sqrt Q)^p.val.val*(Real.sqrt (mixtureCoefficients μ p)*
      |(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u)|) := by ring
    _≤(Real.sqrt Q)^p.val.val*((Real.sqrt (mixtureCoefficients μ p)*(p.val.val : ℝ)*blockThreshold p)*
        Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)) :=
      mul_le_mul_of_nonneg_left (original_latitude_leading_degree_abs_le μ J hJ u hu p hr) (by positivity)
    _=_ := by ring

/-- Literal center-field mean has a genuine uniform source-scale bound
on the actual shared original-disorder Gaussian event. -/
theorem actual_center_latitudeObservableMean_uniform_bound {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) (J : Disorder (n+1) μ.maxDegree)
    (hJ : J∈originalLatitudeMeanGood n μ) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (centerCoefficients (mixtureCoefficients μ) Q) J u (latitudeFrameAt u) r|≤
      centerLatitudeMeanConstant μ Q*(Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+1) := by
  have hpoly := actual_latitudeObservableMean_eq_originalPolynomial_derivative hn
    (centerCoefficients (mixtureCoefficients μ) Q) J u hu hr
  rw [hpoly,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _≤∑ p : Degree μ.maxDegree,
        ((Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*(p.val.val : ℝ)*blockThreshold p)*
          Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*latitudeCorrectionUniformConstant p.val.val) := by
      apply Finset.sum_le_sum
      intro p hp
      have he : (1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*(Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*
          ((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u+
            deriv (pairedLatitudeCorrection n p.val.val (J p) u) r))=
          Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*
            ((1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u))+
          Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*
            ((1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*deriv (pairedLatitudeCorrection n p.val.val (J p) u) r) := by ring
      rw [he]
      apply (abs_add_le _ _).trans
      have ha (t : ℝ) : |Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*t|=
          Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*|t| := by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [ha,ha]
      apply add_le_add (center_latitude_leading_degree_abs_le μ hQ J hJ.1 u hu p (abs_lt.mpr hr).le)
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact (normalized_weighted_pairedLatitudeCorrection_derivative_abs_le hn (J p) u hu (abs_lt.mpr hr).le).trans
        (latitudeCorrectionEnvelope_le_of_not_badBanks (J p) (hJ.2 p))
    _=centerLatitudeLeadingConstant μ Q*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        centerLatitudeCorrectionConstant μ Q := by
      unfold centerLatitudeLeadingConstant centerLatitudeCorrectionConstant
      rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul]
    _≤_ := by
      have hl : 0≤centerLatitudeLeadingConstant μ Q := by
        unfold centerLatitudeLeadingConstant
        exact Finset.sum_nonneg (fun p _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) (blockThreshold_pos p).le)
      have hc : 0≤centerLatitudeCorrectionConstant μ Q := by
        unfold centerLatitudeCorrectionConstant
        exact Finset.sum_nonneg (fun p _ => mul_nonneg (Real.sqrt_nonneg _) (correction_uniform_constant_nonneg _))
      have hv : 0≤Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1) := by positivity
      unfold centerLatitudeMeanConstant
      nlinarith [mul_nonneg hl hv,mul_nonneg hc hv]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
