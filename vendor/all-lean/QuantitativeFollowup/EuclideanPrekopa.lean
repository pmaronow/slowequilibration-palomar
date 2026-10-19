module
public import QuantitativeFollowup.LogConcaveMarginal
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

/-! The genuine Prékopa theorem in Euclidean coordinates. The canonical
coordinate equivalence preserves volume, so no Jacobian or normalization
constant is suppressed. -/
noncomputable section
open MeasureTheory Set WithLp
namespace QuantitativeFollowup

theorem integral_euclidean_toLp {d : ℕ}
    (f : EuclideanSpace ℝ (Fin (d+1)) → ℝ) :
    (∫ x : Fin (d+1) → ℝ, f (toLp 2 x)) = ∫ x, f x := by
  exact (PiLp.volume_preserving_toLp (Fin (d+1))).integral_comp
    (MeasurableEquiv.toLp 2 (Fin (d+1) → ℝ)).measurableEmbedding f

theorem concaveOn_log_integral_exp_neg_euclidean {d : ℕ}
    (S : Set ℝ) (hS : Convex ℝ S)
    (W : ℝ → EuclideanSpace ℝ (Fin (d+1)) → ℝ)
    (hW : ConvexOn ℝ (S ×ˢ univ) (Function.uncurry W))
    (hm : ∀ t ∈ S, Measurable (W t))
    (hi : ∀ t ∈ S, Integrable (fun x => Real.exp (-W t x))) :
    ConcaveOn ℝ S (fun t => Real.log (∫ x, Real.exp (-W t x))) := by
  let e : (Fin (d+1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (d+1)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d+1) => ℝ)).symm
  let L : ℝ × (Fin (d+1) → ℝ) →ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin (d+1)) :=
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap e.toLinearMap
  have hcv : ConvexOn ℝ (S ×ˢ (univ : Set (Fin (d+1) → ℝ)))
      (Function.uncurry (fun t x => W t (toLp 2 x))) := by
    convert hW.comp_linearMap L using 1
    · ext p
      simp [L]
    · rfl
  have hm' (t : ℝ) (ht : t ∈ S) : Measurable (fun x : Fin (d+1) → ℝ => W t (toLp 2 x)) :=
    (hm t ht).comp e.continuous.measurable
  have hi' (t : ℝ) (ht : t ∈ S) :
      Integrable (fun x : Fin (d+1) → ℝ => Real.exp (-W t (toLp 2 x))) := by
    exact (PiLp.volume_preserving_toLp (Fin (d+1))).integrable_comp_of_integrable
      (hi t ht)
  have hh := concaveOn_log_integral_exp_neg S hS (fun t x => W t (toLp 2 x))
    hcv hm' hi'
  convert hh using 1
  funext t
  rw [integral_euclidean_toLp (fun x => Real.exp (-W t x))]

end QuantitativeFollowup
