-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationNormBounds

/-! Genuine full-coefficient Hessian/normalized observation couplings at
arbitrary overlap. These are exact literal coefficient lift terms. -/
@[expose] public section
namespace SlowEquilibration.HessianObservationCovariance
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance ScalarCoefficientCovariance PairObservationNormBounds
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma scalarCross_right_dual {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : E →L[ℝ] ℝ) (A : E →L[ℝ] F) (w : F) :
    scalarCross f ((innerSL ℝ w).comp A)=f (A.adjoint w) := by
  simp only [scalarCross,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one]

/-- Exact actual Hessian coupling to the normalized mixed observation at y. -/
theorem hessian_mixed_coupling {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y u v : Vector N) (f : Fin m → Vector N) (w : MixedObservationSpace m) :
    let r:=overlap x y
    let W:=frameSum f w.snd
    flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint w)=
      (w.fst 0/Real.sqrt (N:ℝ))*
        (secondCovariance c r/(N:ℝ)*inner ℝ u y*inner ℝ v y)+
      (w.fst 1/Real.sqrt (N:ℝ))*
        ((2*secondCovariance c r+r*thirdCovariance c r)/(N:ℝ)*inner ℝ u y*inner ℝ v y)+
      thirdCovariance c r/(N:ℝ)^2*inner ℝ x W*inner ℝ u y*inner ℝ v y+
      secondCovariance c r/(N:ℝ)*(inner ℝ u W*inner ℝ v y+inner ℝ u y*inner ℝ v W) := by
  dsimp only
  rw [← scalarCross_right_dual,singleMixedObservation_dual]
  simp only [scalarCross_add_right,scalarCross_smul_right,scalarCross_flatJet]
  rw [hessian_value_covariance hN c hc x y,
    hessian_radial_covariance hN c hc hdeg x y,
    hessian_gradient_covariance hN c hc hdeg x y]
  ring

/-- Proper value-only Hessian coupling; valid for pure models without a
redundant radial observation. -/
theorem hessian_value_coupling {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y u v : Vector N) (f : Fin m → Vector N) (w : ValueObservationSpace m) :
    let r:=overlap x y
    let W:=frameSum f w.snd
    flatJetCLM c 2 x ![u,v] ((singleValueObservation c y f).adjoint w)=
      (w.fst/Real.sqrt (N:ℝ))*
        (secondCovariance c r/(N:ℝ)*inner ℝ u y*inner ℝ v y)+
      thirdCovariance c r/(N:ℝ)^2*inner ℝ x W*inner ℝ u y*inner ℝ v y+
      secondCovariance c r/(N:ℝ)*(inner ℝ u W*inner ℝ v y+inner ℝ u y*inner ℝ v W) := by
  dsimp only
  rw [← scalarCross_right_dual,singleValueObservation_dual]
  simp only [scalarCross_add_right,scalarCross_smul_right,scalarCross_flatJet]
  rw [hessian_value_covariance hN c hc x y,hessian_gradient_covariance hN c hc hdeg x y]
  ring

end
end SlowEquilibration.HessianObservationCovariance
