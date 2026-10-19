-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SinglePointFullBorderMeanApproximation
public import SlowEquilibration.SchurDimensionRates

/-! Uniform literal one-point full/bulk determinant comparison at the
source inverse-square-root dimension rate, derived from genuine Gaussian
Schur concentration and the actual exponentially small gap loss. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open NormalizedPairObservations PhysicalCommonBorderMoments GOEPhysicalPotential GOEScaling GOERawMoments
open SchurDimensionRates GOEClippedResolvent
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem actual_single_full_border_mixed_L1_rate {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val) {g ρ Z : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1))) :
    ∃ C:ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (ℓ : ℕ) (x v : Vector (n+3)),
      ‖x‖^2=(n+3:ℕ) → ‖v‖=1 → inner ℝ v x=0 →
      ∀ (e : Fin (n+1) → Vector (n+3)), Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) v=0) →
      ∀ (f : Fin ℓ → Vector (n+3)), Surjective (singleMixedObservation c x f) →
      ∀ w : MixedObservationSpace ℓ,
      ∀ k : ℝ, 2*Real.sqrt (secondCovariance c 1)+g ≤ k → k ≤ Z →
      let A := singleMixedObservation c x f
      let b := secondCovariance c 1
      let m := physicalMean n (n+3) b k
      let s := physicalSchurMultiplier b k
      let D := fun J => fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/m
      let B := fun J => matrixAbsoluteDet n k (hessianMatrix c x e J)/m
      Integrable (fun J => |D J-s*B J|) (coefficientKernel A w) ∧
        (∫ J,|D J-s*B J| ∂coefficientKernel A w) ≤ C/Real.sqrt (n+3:ℕ) ∧
        |(∫ J,D J ∂coefficientKernel A w)-s| ≤ C/Real.sqrt (n+3:ℕ) := by
  let b:=secondCovariance c 1
  let A0:=Real.sqrt (bulkSecondMomentBound b g)
  let D0:=Real.sqrt (fullBorderSecondBound b g ρ Z 0 0)
  let a:=g/Real.sqrt b
  let E0:=32*Real.pi^2/a^2
  have ha : 0 < a:=div_pos hg (Real.sqrt_pos.mpr hb)
  have hA0 : 0 < A0 := by dsimp only [A0,bulkSecondMomentBound];positivity
  have hD0 : 0 ≤ D0:=Real.sqrt_nonneg _
  have hE0 : 0 ≤ E0:=by positivity
  have hρg' : ρ ≤ (g/Real.sqrt b)/2 := by convert hρg using 1 <;> ring
  obtain ⟨K,hK,hRate⟩:=actual_single_clipped_schur_mixed_L2_rate c hc hb hdeg hg hρ hρg'
  let C:=A0*Real.sqrt K+3*E0*(D0+|Z| *A0)
  have hC : 0 < C := by
    apply add_pos_of_pos_of_nonneg (mul_pos hA0 (Real.sqrt_pos.mpr hK))
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hRate,actual_single_full_border_mixed_error_eventually (Z:=Z) c hc hb hdeg hg hρ hρg] with n hn hFull
  intro ℓ x v hx hv hvtan e he htan hve f hA w k hk hkZ
  dsimp only
  have hh:=hFull ℓ x v hx hv hvtan e he htan hve f hA w k hk hkZ
  have hs:=hn ℓ x v hx hv hvtan e he htan hve f hA w k hk
  have hSp : 0 < physicalSchurMultiplier b k:=physicalSchurMultiplier_pos hb (by linarith)
  have hSB : physicalSchurMultiplier b k ≤ |Z|:=
    (physicalSchurMultiplier_bounds hb (by linarith)).2.trans (hkZ.trans (le_abs_self _))
  have hGap:=sqrt_exp_gap_le_inverse_dimension n ha
  have hGain:=inverse_dimension_le_ambient_inverse_sqrt n hE0
  have hNorm : Real.sqrt (K/(n+3:ℕ))=Real.sqrt K/Real.sqrt (n+3:ℕ) := Real.sqrt_div hK.le _
  have hBudget :
      A0*Real.sqrt (∫ J,(actualClippedSchurFactor c x e v k (scaleFactor n (n+3) b*ρ) J-
        physicalSchurMultiplier b k)^2 ∂coefficientKernel (singleMixedObservation c x f) w)+
        (D0+physicalSchurMultiplier b k*A0)*Real.sqrt (Real.exp (-(n+1:ℝ)*a^2/(16*Real.pi^2))) ≤
          C/Real.sqrt (n+3:ℕ) := by
    calc
      _ ≤ A0*Real.sqrt (K/(n+3:ℕ))+(D0+|Z| *A0)*(E0/(n+1:ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs.2) hA0.le
        · exact mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_right hSB hA0.le)) hGap
            (Real.sqrt_nonneg _) (by positivity)
      _ ≤ A0*Real.sqrt (K/(n+3:ℕ))+(D0+|Z| *A0)*(3*E0/Real.sqrt (n+3:ℕ)) := by gcongr
      _=_:=by rw [hNorm];unfold C;ring
  exact ⟨hh.1,hh.2.1.trans hBudget,hh.2.2.trans hBudget⟩

theorem actual_single_full_border_value_L1_rate {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val) {g ρ Z : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1))) :
    ∃ C:ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (ℓ : ℕ) (x v : Vector (n+3)),
      ‖x‖^2=(n+3:ℕ) → ‖v‖=1 → inner ℝ v x=0 →
      ∀ (e : Fin (n+1) → Vector (n+3)), Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) v=0) →
      ∀ (f : Fin ℓ → Vector (n+3)), Surjective (singleValueObservation c x f) →
      ∀ w : ValueObservationSpace ℓ,
      ∀ k : ℝ, 2*Real.sqrt (secondCovariance c 1)+g ≤ k → k ≤ Z →
      let A := singleValueObservation c x f
      let b := secondCovariance c 1
      let m := physicalMean n (n+3) b k
      let s := physicalSchurMultiplier b k
      let D := fun J => fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/m
      let B := fun J => matrixAbsoluteDet n k (hessianMatrix c x e J)/m
      Integrable (fun J => |D J-s*B J|) (coefficientKernel A w) ∧
        (∫ J,|D J-s*B J| ∂coefficientKernel A w) ≤ C/Real.sqrt (n+3:ℕ) ∧
        |(∫ J,D J ∂coefficientKernel A w)-s| ≤ C/Real.sqrt (n+3:ℕ) := by
  let b:=secondCovariance c 1
  let A0:=Real.sqrt (bulkSecondMomentBound b g)
  let D0:=Real.sqrt (fullBorderSecondBound b g ρ Z 0 0)
  let a:=g/Real.sqrt b
  let E0:=32*Real.pi^2/a^2
  have ha : 0 < a:=div_pos hg (Real.sqrt_pos.mpr hb)
  have hA0 : 0 < A0 := by dsimp only [A0,bulkSecondMomentBound];positivity
  have hD0 : 0 ≤ D0:=Real.sqrt_nonneg _
  have hE0 : 0 ≤ E0:=by positivity
  have hρg' : ρ ≤ (g/Real.sqrt b)/2 := by convert hρg using 1 <;> ring
  obtain ⟨K,hK,hRate⟩:=actual_single_clipped_schur_value_L2_rate c hc hb hdeg hg hρ hρg'
  let C:=A0*Real.sqrt K+3*E0*(D0+|Z| *A0)
  have hC : 0 < C := by
    apply add_pos_of_pos_of_nonneg (mul_pos hA0 (Real.sqrt_pos.mpr hK))
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hRate,actual_single_full_border_value_error_eventually (Z:=Z) c hc hb hdeg hg hρ hρg] with n hn hFull
  intro ℓ x v hx hv hvtan e he htan hve f hA w k hk hkZ
  dsimp only
  have hh:=hFull ℓ x v hx hv hvtan e he htan hve f hA w k hk hkZ
  have hs:=hn ℓ x v hx hv hvtan e he htan hve f hA w k hk
  have hSp : 0 < physicalSchurMultiplier b k:=physicalSchurMultiplier_pos hb (by linarith)
  have hSB : physicalSchurMultiplier b k ≤ |Z|:=
    (physicalSchurMultiplier_bounds hb (by linarith)).2.trans (hkZ.trans (le_abs_self _))
  have hGap:=sqrt_exp_gap_le_inverse_dimension n ha
  have hGain:=inverse_dimension_le_ambient_inverse_sqrt n hE0
  have hNorm : Real.sqrt (K/(n+3:ℕ))=Real.sqrt K/Real.sqrt (n+3:ℕ) := Real.sqrt_div hK.le _
  have hBudget :
      A0*Real.sqrt (∫ J,(actualClippedSchurFactor c x e v k (scaleFactor n (n+3) b*ρ) J-
        physicalSchurMultiplier b k)^2 ∂coefficientKernel (singleValueObservation c x f) w)+
        (D0+physicalSchurMultiplier b k*A0)*Real.sqrt (Real.exp (-(n+1:ℝ)*a^2/(16*Real.pi^2))) ≤
          C/Real.sqrt (n+3:ℕ) := by
    calc
      _ ≤ A0*Real.sqrt (K/(n+3:ℕ))+(D0+|Z| *A0)*(E0/(n+1:ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs.2) hA0.le
        · exact mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_right hSB hA0.le)) hGap
            (Real.sqrt_nonneg _) (by positivity)
      _ ≤ A0*Real.sqrt (K/(n+3:ℕ))+(D0+|Z| *A0)*(3*E0/Real.sqrt (n+3:ℕ)) := by gcongr
      _=_:=by rw [hNorm];unfold C;ring
  exact ⟨hh.1,hh.2.1.trans hBudget,hh.2.2.trans hBudget⟩

end
end SlowEquilibration.SphericalCommonHessianRegression
