-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemigroupCoreLaplace
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! A genuine positive-rate Laplace integral of a strongly continuous
contraction semigroup. This supplies arbitrarily small physical rates by
actual time rescaling, rather than a lower bound on the rate. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SemigroupLaplace.Data
open Set MeasureTheory Filter
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : SlowEquilibration.SemigroupLaplace.Data E)
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def timeRescale (θ : ℝ≥0) : SlowEquilibration.SemigroupLaplace.Data E where
  P t := S.P (t / θ)
  zero := by simpa using S.zero
  add s t := by rw [add_div,S.add]
  norm_le t x := S.norm_le (t/θ) x
  continuous x := (S.continuous x).comp (by fun_prop)

/-- The actual Bochner integral at the literal physical rate θ. -/
def rateOperator (θ : ℝ≥0) : E →L[ℝ] E :=
  (θ : ℝ)⁻¹ • (S.timeRescale θ).operator

omit [CompleteSpace E] in
theorem rateOperator_norm_le (θ : ℝ≥0) :
    ‖S.rateOperator θ‖ ≤ (θ : ℝ)⁻¹ := by
  rw [rateOperator,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr θ.coe_nonneg)]
  exact mul_le_of_le_one_right (inv_nonneg.mpr θ.coe_nonneg)
    (S.timeRescale θ).operator_norm_le

omit [CompleteSpace E] in
/-- Exact identification with the original semigroup and original time
variable; θ may be exponentially small. -/
theorem rateOperator_integral (θ : ℝ≥0) (hθ : 0 < θ) (x : E) :
    S.rateOperator θ x =
      ∫ t : ℝ in Ioi 0, Real.exp (-(θ : ℝ)*t) • S.P t.toNNReal x := by
  have hθr : 0 < (θ : ℝ) := hθ
  let g : ℝ → E := fun t => Real.exp (-(θ : ℝ)*t) • S.P t.toNNReal x
  have hi := integral_comp_mul_right_Ioi' g 0 (inv_pos.mpr hθr)
  change (θ : ℝ)⁻¹ • (∫ t : ℝ in Ioi 0, g (t*(θ : ℝ)⁻¹)) = ∫ t : ℝ in Ioi (0*(θ : ℝ)⁻¹),g t at hi
  rw [zero_mul] at hi
  change (θ : ℝ)⁻¹ • (∫ t : ℝ in Ioi 0,
    Real.exp (-t) • S.P (t.toNNReal/θ) x) = _
  rw [← hi]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun t => by
    dsimp only [g]
    rw [show -(θ : ℝ)*(t*(θ : ℝ)⁻¹) = -t by field_simp]
    rw [← div_eq_mul_inv,Real.toNNReal_div' θ.coe_nonneg,Real.toNNReal_coe])

omit [CompleteSpace E] in
theorem timeRescale_hasDerivWithinAt_zero (θ : ℝ≥0) (hθ : 0 < θ) (x v : E)
    (hd : HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal x) v (Ici 0) 0) :
    HasDerivWithinAt (fun r : ℝ => (S.timeRescale θ).P r.toNNReal x)
      ((θ : ℝ)⁻¹ • v) (Ici 0) 0 := by
  have hθr : 0 < (θ : ℝ) := hθ
  have hdiv : HasDerivWithinAt (fun r : ℝ => r/(θ : ℝ)) ((θ : ℝ)⁻¹) (Ici 0) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).div_const (θ : ℝ)).hasDerivWithinAt using 1 <;>
      simp only [id_eq,one_div]
  have hc := hd.scomp_of_eq 0 hdiv
    (show MapsTo (fun r : ℝ => r/(θ : ℝ)) (Ici 0) (Ici 0) from
      fun r hr => div_nonneg hr hθr.le) (by simp)
  simpa only [Function.comp_def,timeRescale,Real.toNNReal_div' θ.coe_nonneg,
    Real.toNNReal_coe] using hc

theorem rateOperator_of_derivative_zero (θ : ℝ≥0) (hθ : 0 < θ) (x v : E)
    (hd : HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal x) v (Ici 0) 0) :
    S.rateOperator θ ((θ : ℝ) • x-v)=x := by
  have hθr : (θ : ℝ) ≠ 0 := ne_of_gt (show 0 < (θ : ℝ) from hθ)
  have hh := (S.timeRescale θ).operator_of_derivative_zero x ((θ : ℝ)⁻¹ • v)
    (S.timeRescale_hasDerivWithinAt_zero θ hθ x v hd)
  rw [map_smul] at hh
  change (θ : ℝ)⁻¹ • ((S.timeRescale θ).operator ((θ : ℝ) • x-v))=x
  rw [map_sub,map_smul,smul_sub,smul_smul,inv_mul_cancel₀ hθr,one_smul,hh]
  abel

/-- An actual differential core identifies the Laplace integral at every
strictly positive rate on the entire original closed-generator domain. -/
theorem rateOperator_add_generator (θ : ℝ≥0) (hθ : 0 < θ)
    (A : E →ₗ.[ℝ] E) (hA : A.IsClosed) (C : Submodule ℝ E) (hC : A.HasCore C)
    (hd : ∀ x : C, HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal x)
      (-A ⟨x,hC.le_domain x.property⟩) (Ici 0) 0) (x : A.domain) :
    S.rateOperator θ ((θ : ℝ) • (x : E)+A x)=x := by
  let F : Set (E×E) := {z | S.rateOperator θ ((θ : ℝ) • z.1+z.2)=z.1}
  have hF : IsClosed F := isClosed_eq
    ((S.rateOperator θ).continuous.comp ((continuous_fst.const_smul (θ : ℝ)).add continuous_snd))
    continuous_fst
  have hsub : ((A.domRestrict C).graph : Set (E×E)) ⊆ F := by
    intro z hz
    obtain ⟨y,hy,hAy⟩ := (A.domRestrict C).mem_graph_iff.mp hz
    have he := S.rateOperator_of_derivative_zero θ hθ (y : E)
      (-A ⟨y,hC.le_domain y.property.1⟩) (hd ⟨y,y.property.1⟩)
    change S.rateOperator θ ((θ : ℝ) • z.1+z.2)=z.1
    rw [← hy,← hAy]
    rw [LinearPMap.domRestrict_apply (show (y : E)=(⟨y,hC.le_domain y.property.1⟩ : A.domain) from rfl)]
    simpa only [sub_neg_eq_add] using he
  have hclosable := hA.isClosable.leIsClosable
    (show A.domRestrict C ≤ A from LinearPMap.domRestrict_le)
  have heq : (A.domRestrict C).graph.topologicalClosure=A.graph := by
    rw [hclosable.graph_closure_eq_closure_graph,hC.closure_eq]
  have hs := closure_minimal hsub hF
  have hx : ((x : E),A x)∈closure ((A.domRestrict C).graph : Set (E×E)) := by
    change ((x : E),A x)∈(A.domRestrict C).graph.topologicalClosure
    rw [heq]
    exact A.mem_graph x
  exact hs hx

end SlowEquilibration.SemigroupLaplace.Data
