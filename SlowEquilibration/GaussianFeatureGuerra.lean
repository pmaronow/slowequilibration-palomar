-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureCubePositivity
public import SlowEquilibration.GaussianFeatureEndpoints

/-! True finite spherical-feature Guerra bound with a fixed finite held
positivity bank. The covariance and deterministic tangent deficit refer
to the original actual feature; Gaussian positivity is derived internally. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open SphericalPositivePerturbation
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def trialVariance (n : ℕ) (β d : ℝ) : ℝ := β^2*((n+1:ℕ):ℝ)/(n:ℝ)*d

theorem trialVariance_nonneg (n : ℕ) (β : ℝ) {d : ℝ} (hd : 0≤d) : 0≤trialVariance n β d := by
  unfold trialVariance
  positivity

theorem trialVariance_mul_dim (hn : 1≤n) (β d : ℝ) :
    trialVariance n β d*(n:ℝ)=β^2*((n+1:ℕ):ℝ)*d := by
  unfold trialVariance
  have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Literal signed covariance computed from the supplied actual Gram law. -/
theorem three_signedKernel_covariance {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι) (ξ : ℝ → ℝ)
    (hGram : ∀x y : Vector n,‖x‖^2=(n:ℝ) → ‖y‖^2=(n:ℝ) →
      inner ℝ (A x) (A y)=((n+1:ℕ):ℝ)*ξ (SphericalModel.overlap x y))
    (β : ℝ) {k : ℝ} (hk : 0≤k) (W : Vector n → EuclideanSpace ℝ κ)
    (x y : Vector n) (hx : ‖x‖^2=(n:ℝ)) (hy : ‖y‖^2=(n:ℝ)) :
    GaussianThreeBlockComparison.signedKernel (threeLinear A β k W) threeLabel x y=
      k*(n:ℝ)*SphericalModel.overlap x y-β^2*((n+1:ℕ):ℝ)*ξ (SphericalModel.overlap x y) := by
  rw [three_signedKernel_eq,two_signedKernel A β hk,hGram x y hx hy]
  have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  unfold SphericalModel.overlap
  field_simp

/-- A fixed genuine perturbation strength, chosen before every dimension,
original feature space/realization and covariance family, gives a fully
actual finite-volume Guerra inequality with explicit normalized errors. -/
theorem exists_uniform_finite_Guerra_error {η ζ : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hζ : 0<ζ) :
    ∃ V : ℝ,1≤V ∧ ∀ (n : ℕ),1≤n →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∀ (A : Vector n → EuclideanSpace ℝ ι),Continuous A →
      ∀ (β : ℝ) (ξ : ℝ → ℝ) (t d C : ℝ),0≤d → 0≤C →
      (∀x y : Vector n,‖x‖^2=(n:ℝ) → ‖y‖^2=(n:ℝ) →
        inner ℝ (A x) (A y)=((n+1:ℕ):ℝ)*ξ (SphericalModel.overlap x y)) →
      (∀R∈Icc (-1:ℝ) 1,ξ t+d*(R-t)-ξ R≤C*({r : ℝ | r< -η}.indicator (fun _ => (1:ℝ))) R) →
      pressure A β≤(n:ℝ)/((n+1:ℕ):ℝ)*SphericalModel.linearSphereQuenchedPressure n (trialVariance n β d)+
        β^2/2*(ξ 1-ξ t-(1-t)*d)+β^2*C*ζ/2+2*V^2/((n+1:ℕ):ℝ) := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_cube_pair_positivity hη hη1 hζ
  refine ⟨V,hV,?_⟩
  intro n hn ι _ _ A hA β ξ t d C hd hC hGram hDef
  have hv : 0≤V := (by norm_num : (0:ℝ)≤1).trans hV
  let k := trialVariance n β d
  have hk : 0≤k := trialVariance_nonneg n β hd
  let L := cubeLinear (K := K) A β k V
  let E : Set (Vector n × Vector n) := {z | SphericalModel.overlap z.1 z.2≤-η}
  have hE : MeasurableSet E := by
    have hm : Measurable (fun z : Vector n × Vector n => SphericalModel.overlap z.1 z.2) := by
      unfold SphericalModel.overlap
      fun_prop
    exact measurableSet_le hm measurable_const
  let c := β^2*((n+1:ℕ):ℝ)*(d*t-ξ t)
  let a := β^2*((n+1:ℕ):ℝ)*C
  let Δ := k*(n:ℝ)-β^2*((n+1:ℕ):ℝ)*ξ 1
  have ha : 0≤a := by dsimp [a];positivity
  have hL (cube : Fin K → ℝ) : Measurable (L cube) := (cubeLinear_continuous A hA β k V cube).measurable
  have hpair (cube : Fin K → ℝ) : ∀ᵐ z ∂(sphereLaw n).prod (sphereLaw n),
      GaussianThreeBlockComparison.signedKernel (L cube) threeLabel z.1 z.2≤c+a*E.indicator (fun _ => (1:ℝ)) z := by
    filter_upwards [SphericalModel.sphereLaw_prod_support hn] with z hz
    have hr := SphericalModel.overlap_mem_Icc_of_norm_sq hn z.1 z.2 hz.1 hz.2
    have ht := mul_le_mul_of_nonneg_left (hDef (SphericalModel.overlap z.1 z.2) hr)
      (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg (n+1)))
    have hKer := three_signedKernel_covariance hn A ξ hGram β hk (cubeFeature n K V cube) z.1 z.2 hz.1 hz.2
    have hI : ({r : ℝ | r< -η}.indicator (fun _ => (1:ℝ))) (SphericalModel.overlap z.1 z.2)≤
        E.indicator (fun _ => (1:ℝ)) z := by
      by_cases hr : SphericalModel.overlap z.1 z.2< -η
      · have hc : SphericalModel.overlap z.1 z.2≤-η := hr.le
        simp [E,hr,hc]
      · by_cases hc : SphericalModel.overlap z.1 z.2≤-η <;> simp [E,hr,hc]
    have hIs := mul_le_mul_of_nonneg_left hI ha
    dsimp only [L,c,a,cubeLinear] at hIs ⊢
    rw [hKer,show k*(n:ℝ)=β^2*((n+1:ℕ):ℝ)*d from trialVariance_mul_dim hn β d]
    nlinarith
  have hNeg (θ : ℝ) : (∫cube,∫D,GaussianThreeBlockComparison.pairEventMass
      (sphereLaw n) (L cube) threeLabel θ E D
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)) ∂positiveCubeLaw K)≤ζ :=
    hPos n hn ι A hA β k V le_rfl θ
  have hMean (θ : ℝ) : GaussianThreeBlockComparison.parameterAveragedPairKernel
      (positiveCubeLaw K) (sphereLaw n) L threeLabel θ≤c+a*ζ := by
    let f := fun cube : Fin K → ℝ => ∫D,GaussianThreeBlockComparison.pairEventMass
      (sphereLaw n) (L cube) threeLabel θ E D
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K))
    have hf : Integrable f (positiveCubeLaw K) := cube_meanEventMass_integrable hn A hA β k V θ E hE
    have hi := cube_meanPair_integrable (K := K) hn A hA β k hv θ
    have hb : ∀ᵐ cube ∂positiveCubeLaw K,
        GaussianThreeBlockComparison.meanPairKernel (sphereLaw n) (L cube) threeLabel θ≤c+a*f cube := .of_forall fun cube => by
      obtain ⟨B,hB,hbound⟩ := exists_cube_bound hn A hA β k V cube
      exact GaussianThreeBlockComparison.meanPairKernel_le_of_indicator (sphereLaw n) (L cube) (hL cube)
        hB hbound threeLabel E hE (hpair cube) θ
    have hh := integral_mono_ae hi ((integrable_const c).add (hf.const_mul a)) hb
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const c) (hf.const_mul a),integral_const_mul a f] at hh
    simp only [integral_const,probReal_univ,one_smul] at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hNeg θ) ha))
  obtain ⟨B,hB,hUniform⟩ := exists_uniform_cube_bound (K := K) hn A hA β k hv
  have hLb : ∀ᵐ cube ∂positiveCubeLaw K,∀ᵐ x ∂sphereLaw n,‖L cube x‖≤B :=
    (positiveCubeLaw_abs_le_two K).mono fun cube hc => hUniform cube hc
  have hDiag : ∀ᵐ cube ∂positiveCubeLaw K,∀ᵐ x ∂sphereLaw n,
      GaussianThreeBlockComparison.signedKernel (L cube) threeLabel x x=Δ := .of_forall fun cube => by
    filter_upwards [sphereLaw_support hn] with x hx
    change GaussianThreeBlockComparison.signedKernel (threeLinear A β k (cubeFeature n K V cube)) threeLabel x x=Δ
    rw [three_signedKernel_covariance hn A ξ hGram β hk _ x x hx hx,SphericalModel.overlap_self hn x hx,mul_one]
  have hc := GaussianThreeBlockComparison.gaussian_covariance_comparison_of_parameter_mean_pair
    (positiveCubeLaw K) (sphereLaw n) L hL hB hLb threeLabel hDiag
    (fun θ => (cube_pressure_measurable hn A hA β k V θ).aestronglyMeasurable)
    (fun θ => cube_meanPair_integrable hn A hA β k hv θ) (fun θ _ => hMean θ)
  have hLeft := (cube_pressure_sub_twoMean_mem_Icc (K := K) hn A hA β k hv 0).1
  have hRight := (cube_pressure_sub_twoMean_mem_Icc (K := K) hn A hA β k hv (Real.pi/2)).2
  have hh : GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel 0≤
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel (Real.pi/2)+
        (c-Δ)/2+a*ζ/2+2*V^2 := by linarith
  rw [twoMean_zero_eq_original hn A hA β k,twoMean_pi_div_two_eq_linear hn A β hk] at hh
  have hNpos : 0<((n+1:ℕ):ℝ) := by positivity
  have hh' := div_le_div_of_nonneg_right hh hNpos.le
  have heq : ((n:ℝ)*SphericalModel.linearSphereQuenchedPressure n k+(c-Δ)/2+a*ζ/2+2*V^2)/((n+1:ℕ):ℝ)=
      (n:ℝ)/((n+1:ℕ):ℝ)*SphericalModel.linearSphereQuenchedPressure n k+
        β^2/2*(ξ 1-ξ t-(1-t)*d)+β^2*C*ζ/2+2*V^2/((n+1:ℕ):ℝ) := by
    dsimp [c,Δ,a,k]
    rw [trialVariance_mul_dim hn β d]
    field_simp
    ring
  rw [heq] at hh'
  exact hh'

end SlowEquilibration.GaussianFeatureDirac
