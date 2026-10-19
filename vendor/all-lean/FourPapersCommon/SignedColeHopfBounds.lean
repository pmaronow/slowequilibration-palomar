module
public import FourPapersCommon.SignedColeHopfDatum
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Global spatial Lipschitz regularity of the genuine signed heat feedback. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FRSB
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000

theorem SignedScalarDatum.hasDerivAt_deriv {A : ℝ → ℝ} (hA : SignedScalarDatum A) (x : ℝ) :
    HasDerivAt (deriv A) (iteratedDeriv 2 A x) x := by
  have hh := (hA.smooth.differentiable_iteratedDeriv 1 (by norm_num) x).hasDerivAt
  convert! hh using 1 <;> simp only [iteratedDeriv_succ,iteratedDeriv_zero]

theorem signedHeatLogDxx_exp_eq_tilt {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (m v x : ℝ) (hm : m≠0) :
    signedHeatLogDxx (fun y=>Real.exp (m*A y)) m v x=
      (∫ z,(iteratedDeriv 2 A (x+z)+m*(deriv A (x+z))^2)*
        coleHopfQ m v.toNNReal A x z ∂gaussianReal 0 v.toNNReal)-
      m*(signedHeatLogDx (fun y=>Real.exp (m*A y)) m v x)^2 := by
  obtain ⟨L,hL⟩ := hA.lipschitz
  obtain ⟨K,hK⟩ := hA.second_bound
  have hG1 : HasExpGrowth (deriv A) := HasExpGrowth.of_bounded (fun y=>by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀:=y) hL)
  have hG2 : HasExpGrowth (iteratedDeriv 2 A) := HasExpGrowth.of_bounded hK
  have hd := hasDerivAt_signedHeatLogDx (hA.expHeatDatum m) m v x hm
    (gaussianHeatFlow_exp_pos hA m v x).ne'
  have hd' := hasDerivAt_integral_deriv_mul_coleHopfQ
    (fun y=>(hA.smooth.differentiable (by norm_num) y).hasDerivAt)
    hA.hasDerivAt_deriv hA.linearGrowth hG1 hG2
    (hA.smooth.continuous_iteratedDeriv 2 (by norm_num)).measurable hm v.toNNReal x
  have he : signedHeatLogDx (fun y=>Real.exp (m*A y)) m v=
      fun y=>∫ z,deriv A (y+z)*coleHopfQ m v.toNNReal A y z ∂gaussianReal 0 v.toNNReal :=
    funext (fun y=>signedHeatLogDx_exp_eq_tilt hA m v y hm)
  rw [he] at hd
  rw [signedHeatLogDx_exp_eq_tilt hA m v x hm]
  exact hd.unique hd'

theorem norm_signedHeatLogDxx_exp_le {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (L : ℝ≥0) (hL : LipschitzWith L A) (K : ℝ)
    (hK : ∀ x,|iteratedDeriv 2 A x|≤K) (m v x : ℝ) (hm : m≠0) :
    ‖signedHeatLogDxx (fun y=>Real.exp (m*A y)) m v x‖≤K+2*|m| *(L:ℝ)^2 := by
  let G := fun y=>iteratedDeriv 2 A y+m*(deriv A y)^2
  have hGb : ∀ y,|G y|≤K+|m| *(L:ℝ)^2 := by
    intro y
    have hf : |deriv A y|≤L := by
      simpa only [Real.norm_eq_abs] using
        norm_deriv_le_of_lipschitz (x₀:=y) hL
    calc
      _ ≤ |iteratedDeriv 2 A y|+|m*(deriv A y)^2| := abs_add_le _ _
      _ ≤ K+|m| *(L:ℝ)^2 := by
        rw [abs_mul,abs_pow]
        gcongr
        exact hK y
  have hGm : Measurable G :=
    (hA.smooth.continuous_iteratedDeriv 2 (by norm_num)).measurable.add
      (measurable_const.mul ((hA.smooth.continuous_deriv (by norm_num)).measurable.pow_const 2))
  have hi := abs_integral_mul_coleHopfQ_le hA.linearGrowth hA.smooth.continuous.measurable
    hm hGm hGb v.toNNReal x
  have hx := norm_signedHeatLogDx_exp_le hA L hL m v x hm
  rw [signedHeatLogDxx_exp_eq_tilt hA m v x hm,Real.norm_eq_abs]
  calc
    _ ≤ |∫ z,G (x+z)*coleHopfQ m v.toNNReal A x z ∂gaussianReal 0 v.toNNReal|+
        |m*(signedHeatLogDx (fun y=>Real.exp (m*A y)) m v x)^2|  := by
          simpa only [Real.norm_eq_abs,G] using
            (norm_sub_le (∫ z,G (x+z)*coleHopfQ m v.toNNReal A x z ∂gaussianReal 0 v.toNNReal)
              (m*(signedHeatLogDx (fun y=>Real.exp (m*A y)) m v x)^2))
    _ ≤ (K+|m| *(L:ℝ)^2)+|m| *(L:ℝ)^2 := by
      rw [abs_mul,abs_pow]
      gcongr
      simpa only [Real.norm_eq_abs] using hx
    _ = _ := by ring

theorem exists_lipschitz_signedHeatLogDx_exp {A : ℝ → ℝ} (hA : SignedScalarDatum A)
    (m : ℝ) (hm : m≠0) :
    ∃ K : ℝ≥0,∀ v,LipschitzWith K (signedHeatLogDx (fun y=>Real.exp (m*A y)) m v) := by
  obtain ⟨L,hL⟩ := hA.lipschitz
  obtain ⟨K,hK⟩ := hA.second_bound
  have hK0 : 0≤K := (abs_nonneg _).trans (hK 0)
  let C : ℝ≥0 := ⟨K+2*|m| *(L:ℝ)^2,by positivity⟩
  refine ⟨C,fun v=>?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_signedHeatLogDx (hA.expHeatDatum m) m v x hm
      (gaussianHeatFlow_exp_pos hA m v x).ne').differentiableAt
  · intro x
    rw [(hasDerivAt_signedHeatLogDx (hA.expHeatDatum m) m v x hm
      (gaussianHeatFlow_exp_pos hA m v x).ne').deriv]
    exact norm_signedHeatLogDxx_exp_le hA L hL K hK m v x hm

end FourPapersCommon
