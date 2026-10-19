-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ValueObservationSmallOverlap

/-! The actual two complete tangent gradients form a genuinely surjective
Gaussian observation on a dimension-uniform small-overlap neighborhood. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pairGradient {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m)×EuclideanSpace ℝ (Fin m)) :=
  pairHilbert (gradientCLM c x e) (gradientCLM c y f)

/-- Every true gradient pair target is achieved by an actual value/gradient
pair witness. No independent radial observation is used. -/
lemma pairGradient_surjective_of_valuePair {N P m : ℕ} (c : Degree P → ℝ)
    (x y : Vector N) (e f : Fin m → Vector N)
    (hA : Surjective (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))) :
    Surjective (pairGradient c x y e f) := by
  intro w
  let v : WithLp 2 (ValueObservationSpace m×ValueObservationSpace m):=
    WithLp.toLp 2 (WithLp.toLp 2 (0,w.fst),WithLp.toLp 2 (0,w.snd))
  obtain ⟨z,hz⟩:=hA v
  refine ⟨z,?_⟩
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact congrArg (fun q => q.fst.snd) hz
  · exact congrArg (fun q => q.snd.snd) hz

end
end SlowEquilibration.NormalizedPairObservations

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine pair gradient nondegeneracy, chosen before every spatial
dimension, point pair, frame and gradient target. -/
theorem uniform_pair_gradient_surjective (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      Surjective (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_value_pair_nondegenerate μ hQ hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hr
  exact pairGradient_surjective_of_valuePair _ x y e f
    (hall N m hN x y hx hy e f he hf htanx htany hr).2.1

end
end SlowEquilibration.PairObservationSmallOverlap
