-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureLinearUniform

/-! Generic actual finite-feature spherical Dirac upper, uniformly over
compact scalar families and every original Gaussian feature realization.
No pressure asymptotics, positivity law or Gaussian comparison is an input. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set Filter
open SphericalAging.FiniteModel
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def diracTrial (β : ℝ) (ξ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (β^2*(ξ 1-ξ t)+t/(1-t)+Real.log (1-t))/2

/-- Every feature realization has the genuine Dirac upper once its actual
Gram and deterministic covariance tangent error are identified. The
threshold precedes n, all finite coefficient types, and all features;
no joint feature continuity or coordinate-cardinality bound is required.
Constant and linear covariance terms are retained literally. -/
theorem eventually_uniform_dirac_upper {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (β : ℝ) (ξ : Z → ℝ → ℝ) (t d : Z → ℝ) (ht : Continuous t) (hd : Continuous d)
    (htrange : ∀z,t z∈Ico (0:ℝ) 1) (hdnonneg : ∀z,0≤d z)
    {η C : ℝ} (hη : 0<η) (hη1 : η≤1) (hC : 0≤C)
    (hDef : ∀z : Z,∀R∈Icc (-1:ℝ) 1,
      ξ z (t z)+d z*(R-t z)-ξ z R≤C*({r : ℝ | r< -η}.indicator (fun _ => (1:ℝ))) R)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀z : Z,∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∀ (A : Vector n → EuclideanSpace ℝ ι),Continuous A →
      (∀x y : Vector n,‖x‖^2=(n:ℝ) → ‖y‖^2=(n:ℝ) →
        inner ℝ (A x) (A y)=((n+1:ℕ):ℝ)*ξ z (SphericalModel.overlap x y)) →
      pressure A β≤diracTrial β (ξ z) (t z)+ε := by
  let ζ := ε/(2*(β^2*C+1))
  have hζ : 0<ζ := by dsimp [ζ];positivity
  have hζeq : 2*(β^2*C+1)*ζ=ε := by dsimp [ζ];field_simp
  have hζsmall : β^2*C*ζ/2≤ε/4 := by nlinarith [hζ.le]
  obtain ⟨V,hV,hGuerra⟩ := exists_uniform_finite_Guerra_error hη hη1 hζ
  have hCost := ((tendsto_const_div_atTop_nhds_zero_nat (2*V^2)).comp
    (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (by positivity : 0<ε/4))
  have hLinear := eventually_uniform_linear_Dirac_upper β d t hd ht hdnonneg htrange
    (by positivity : 0<ε/4)
  filter_upwards [hCost,hLinear,eventually_ge_atTop 1] with n hCost hLinear hn
  dsimp only [Function.comp_def] at hCost
  intro z ι _ _ A hA hGram
  have hg := hGuerra n hn ι A hA β (ξ z) (t z) (d z) C (hdnonneg z) hC hGram (hDef z)
  have heq : linearEntropy β (d z) (t z)+β^2/2*(ξ z 1-ξ z (t z)-(1-t z)*d z)=
      diracTrial β (ξ z) (t z) := by unfold linearEntropy diracTrial;ring
  have hl := hLinear z
  rw [← heq]
  linarith

end SlowEquilibration.GaussianFeatureDirac
