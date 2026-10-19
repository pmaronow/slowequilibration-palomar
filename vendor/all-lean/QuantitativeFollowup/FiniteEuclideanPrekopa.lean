module
public import QuantitativeFollowup.EuclideanPrekopa
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! Prékopa log-concavity on any actual nonempty finite Euclidean coordinate
set. The reindexing is an isometry and preserves canonical Lebesgue volume. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem concaveOn_log_integral_exp_neg_finite_euclidean
    (S : Set ℝ) (hS : Convex ℝ S) (W : ℝ→EuclideanSpace ℝ ι→ℝ)
    (hW : ConvexOn ℝ (S ×ˢ univ) (Function.uncurry W))
    (hm : ∀t∈S,Measurable (W t))
    (hi : ∀t∈S,Integrable (fun x => Real.exp (-W t x))) :
    ConcaveOn ℝ S (fun t => Real.log (∫x,Real.exp (-W t x))) := by
  let d := Fintype.card ι-1
  have hc : Fintype.card ι = d+1 := by
    have hh := Fintype.card_pos (α := ι)
    dsimp [d]
    omega
  let e : EuclideanSpace ℝ (Fin (d+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFinOfCardEq hc).symm
  let L : ℝ×EuclideanSpace ℝ (Fin (d+1)) →ₗ[ℝ] ℝ×EuclideanSpace ℝ ι :=
    (LinearMap.id : ℝ→ₗ[ℝ]ℝ).prodMap e.toLinearEquiv.toLinearMap
  have hcv : ConvexOn ℝ (S ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d+1)))))
      (Function.uncurry (fun t x => W t (e x))) := by
    convert hW.comp_linearMap L using 1
    · ext p
      simp [L]
    · rfl
  have hh := concaveOn_log_integral_exp_neg_euclidean S hS (fun t x => W t (e x)) hcv
    (fun t ht => (hm t ht).comp e.continuous.measurable)
    (fun t ht => e.measurePreserving.integrable_comp_of_integrable (hi t ht))
  convert hh using 1
  funext t
  congr 1
  exact (e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => Real.exp (-W t x))).symm

end QuantitativeFollowup
