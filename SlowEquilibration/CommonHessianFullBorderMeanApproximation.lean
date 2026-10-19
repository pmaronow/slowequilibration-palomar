-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianFullBorderSecondMoment
public import SlowEquilibration.CommonHessianActualSchurMeanSquare
public import SlowEquilibration.PhysicalBorderSchurExpectation

/-! Actual original-posterior full bordered determinant error and adjacent
first-mean approximation. Full moments, Schur integrability, true bulk laws
and rare-gap probabilities are all derived inside the model consumers.
-/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression GaussianRegressionCovariance
open NormalizedPairObservations GaussianObservationCoercivity
open PhysicalCommonBorderMoments GOEPhysicalPotential GOEScaling GOEClippedResolvent GOERawMoments
open PairHessianMean PairObservationNormBounds GOEPhysicalGapEvent
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

def bulkSecondMomentBound (b g : ℝ) : ℝ := (2 : ℝ)^2*Real.exp (16*b/g^2)


/-- Literal mixed-pair full determinant approximation, with the true
clipped Schur MSE retained as an ordinary integral of the actual tensor
posterior. The actual Schur and GOE trace theorems bound this term.
-/
theorem actual_common_full_border_mixed_error_eventually {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val) {g ρ Z δ M : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1)))
    (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (ℓ : ℕ) (x y v : Vector (n+3)),
      ‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) → ‖v‖=1 → inner ℝ v x=0 →
      ∀ (e : Fin (n+1) → Vector (n+3)), Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) y=0) → (∀ i,inner ℝ (e i) v=0) →
      ∀ (f h : Fin ℓ → Vector (n+3)), Orthonormal ℝ h → |overlap x y| ≤ 1 →
      Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)) →
      ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h))).inverse‖ ≤ 1/δ →
      ∀ (w : WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ)), ‖w‖ ≤ M*Real.sqrt (n+3:ℕ) →
      ∀ k : ℝ, 2*Real.sqrt (secondCovariance c 1)+g ≤ k → k ≤ Z →
      let A := pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)
      let b := secondCovariance c 1
      let m := physicalMean n (n+3) b k
      let κ := scaleFactor n (n+3) b*ρ
      let s := physicalSchurMultiplier b k
      let D := fun J => fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/m
      let B := fun J => matrixAbsoluteDet n k (hessianMatrix c x e J)/m
      let E := ∫ J,(actualClippedSchurFactor c x e v k κ J-s)^2 ∂coefficientKernel A w
      let R := Real.sqrt (bulkSecondMomentBound b g)*Real.sqrt E+
        (Real.sqrt (fullBorderSecondBound b g ρ Z (7*profileBound c*M/δ) (profileBound c*M/δ))+
          s*Real.sqrt (bulkSecondMomentBound b g))*
            Real.sqrt (Real.exp (-(n+1:ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2)))
      Integrable (fun J => |D J-s*B J|) (coefficientKernel A w) ∧
        (∫ J,|D J-s*B J| ∂coefficientKernel A w) ≤ R ∧
        |(∫ J,D J ∂coefficientKernel A w)-s| ≤ R := by
  filter_upwards [actual_common_border_mixed_second_moment_eventually (Z := Z) c hc hb hdeg hg hρ hρg hδ hM,
    GOESharpMoments.goe_determinant_moments_eventually hb hg,
    physical_gap_failure_eventually hb hg hρ hρg] with n hFullAll hRawAll hGapAll
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  dsimp only
  let A := pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)
  let μ := coefficientKernel A w
  let b := secondCovariance c 1
  let m := physicalMean n (n+3) b k
  let κ := scaleFactor n (n+3) b*ρ
  let s := physicalSchurMultiplier b k
  let D := fun J:Disorder (n+3) P => fullBorder (hessianMatrix c x e) k
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/m
  let B := fun J:Disorder (n+3) P => matrixAbsoluteDet n k (hessianMatrix c x e J)/m
  let E := ∫ J,(actualClippedSchurFactor c x e v k κ J-s)^2 ∂μ
  have hFull := hFullAll ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  have hN : 0 < n+3 := by omega
  have h3 : ∀ p,c p≠0 → 3 ≤ p.val.val := fun p hp => (by omega : 3 ≤ 4).trans (hdeg p hp)
  have hLaw := posterior_common_matrix_mixed_hasLaw hN c hc h3 x y hx e he htanx htany f h w
  have hRaw := hRawAll (n+3) (by omega) k hk
  have hR2 := hRaw.2.2 2 (by norm_num)
  have hB2 : Integrable (fun J => B J^2) μ := by
    simpa only [Real.rpow_two, B, μ, A, m, b, physicalMean, GOESharpMoments.matrixAbsoluteDet, GOERawMoments.matrixAbsoluteDet] using hLaw.integrable_fun_comp hR2.1
  have hBM : (∫ J,B J^2 ∂μ) ≤ bulkSecondMomentBound b g := by
    have hEq := hLaw.integral_comp
      (((matrixAbsoluteDet_measurable n k).div_const m).pow_const (2 : ℕ)).aestronglyMeasurable
    simp only [Function.comp_def] at hEq
    change (∫ J,B J^2 ∂μ)=_ at hEq
    rw [hEq]
    simpa only [Real.rpow_two, bulkSecondMomentBound, m, b, physicalMean, GOESharpMoments.matrixAbsoluteDet, GOERawMoments.matrixAbsoluteDet,
      show 4*b*(2:ℝ)^2/g^2=16*b/g^2 by ring] using hR2.2
  have hSchur := actual_common_clipped_schur_mixed_mse c hc hb (d := 4) (by omega) hdeg
    x y v hx hy hv hvtan e he htanx htany hve f h hh hr hδ hM hρ hA hinv w hw k
  have hκ : 0 < κ := mul_pos (scaleFactor_pos n hN hb) hρ
  have hSym (J : Disorder (n+3) P) : (hessianMatrix c x e J).IsHermitian := by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial,hessianMatrix] using hessianEntry_symm c x e j i J
  have hSpos : 0 < s := physicalSchurMultiplier_pos hb (by linarith)
  have hApprox := normalized_full_border_schur_error hκ (hessianMatrix c x e)
    (tensor_hessianMatrix_measurable c x e) hSym hLaw
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v))
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)
    hFull.1 s hFull.2.1 hB2
    (by simpa only [clippedSchur,actualClippedSchurFactor] using hSchur.1)
    (by change Measurable (actualClippedSchurFactor c x e v k κ); exact actualClippedSchurFactor_measurable c x e v k hκ)
  simp only [abs_of_pos hSpos] at hApprox
  have hMajor :
      Real.sqrt (∫ J,B J^2 ∂μ)*Real.sqrt E+
        (Real.sqrt (∫ J,D J^2 ∂μ)+s*Real.sqrt (∫ J,B J^2 ∂μ))*
          Real.sqrt ((goeLaw (n+1) (n+3) b).real (gapEvent n k κ)ᶜ) ≤
      Real.sqrt (bulkSecondMomentBound b g)*Real.sqrt E+
        (Real.sqrt (fullBorderSecondBound b g ρ Z (7*profileBound c*M/δ) (profileBound c*M/δ))+
          s*Real.sqrt (bulkSecondMomentBound b g))*
            Real.sqrt (Real.exp (-(n+1:ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2))) := by
    have hDM := hFull.2.2
    have hGM := hGapAll (n+3) (by omega) k hk
    gcongr
  refine ⟨hApprox.1,?_,?_⟩
  · exact hApprox.2.1.trans hMajor
  · exact hApprox.2.2.trans hMajor

/-- Literal value-pair full determinant approximation, with the true
clipped Schur MSE retained as an ordinary integral of the actual tensor
posterior. The actual Schur and GOE trace theorems bound this term.
-/
theorem actual_common_full_border_value_error_eventually {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val) {g ρ Z δ M : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1)))
    (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (ℓ : ℕ) (x y v : Vector (n+3)),
      ‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) → ‖v‖=1 → inner ℝ v x=0 →
      ∀ (e : Fin (n+1) → Vector (n+3)), Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) y=0) → (∀ i,inner ℝ (e i) v=0) →
      ∀ (f h : Fin ℓ → Vector (n+3)), Orthonormal ℝ h → |overlap x y| ≤ 1 →
      Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)) →
      ‖(gram (pairHilbert (singleValueObservation c x f) (singleValueObservation c y h))).inverse‖ ≤ 1/δ →
      ∀ (w : WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ)), ‖w‖ ≤ M*Real.sqrt (n+3:ℕ) →
      ∀ k : ℝ, 2*Real.sqrt (secondCovariance c 1)+g ≤ k → k ≤ Z →
      let A := pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)
      let b := secondCovariance c 1
      let m := physicalMean n (n+3) b k
      let κ := scaleFactor n (n+3) b*ρ
      let s := physicalSchurMultiplier b k
      let D := fun J => fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/m
      let B := fun J => matrixAbsoluteDet n k (hessianMatrix c x e J)/m
      let E := ∫ J,(actualClippedSchurFactor c x e v k κ J-s)^2 ∂coefficientKernel A w
      let R := Real.sqrt (bulkSecondMomentBound b g)*Real.sqrt E+
        (Real.sqrt (fullBorderSecondBound b g ρ Z (7*profileBound c*M/δ) (profileBound c*M/δ))+
          s*Real.sqrt (bulkSecondMomentBound b g))*
            Real.sqrt (Real.exp (-(n+1:ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2)))
      Integrable (fun J => |D J-s*B J|) (coefficientKernel A w) ∧
        (∫ J,|D J-s*B J| ∂coefficientKernel A w) ≤ R ∧
        |(∫ J,D J ∂coefficientKernel A w)-s| ≤ R := by
  filter_upwards [actual_common_border_value_second_moment_eventually (Z := Z) c hc hb hdeg hg hρ hρg hδ hM,
    GOESharpMoments.goe_determinant_moments_eventually hb hg,
    physical_gap_failure_eventually hb hg hρ hρg] with n hFullAll hRawAll hGapAll
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  dsimp only
  let A := pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)
  let μ := coefficientKernel A w
  let b := secondCovariance c 1
  let m := physicalMean n (n+3) b k
  let κ := scaleFactor n (n+3) b*ρ
  let s := physicalSchurMultiplier b k
  let D := fun J:Disorder (n+3) P => fullBorder (hessianMatrix c x e) k
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/m
  let B := fun J:Disorder (n+3) P => matrixAbsoluteDet n k (hessianMatrix c x e J)/m
  let E := ∫ J,(actualClippedSchurFactor c x e v k κ J-s)^2 ∂μ
  have hFull := hFullAll ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  have hN : 0 < n+3 := by omega
  have h3 : ∀ p,c p≠0 → 3 ≤ p.val.val := fun p hp => (by omega : 3 ≤ 4).trans (hdeg p hp)
  have hLaw := posterior_common_matrix_value_hasLaw hN c hc h3 x y hx e he htanx htany f h w
  have hRaw := hRawAll (n+3) (by omega) k hk
  have hR2 := hRaw.2.2 2 (by norm_num)
  have hB2 : Integrable (fun J => B J^2) μ := by
    simpa only [Real.rpow_two, B, μ, A, m, b, physicalMean, GOESharpMoments.matrixAbsoluteDet, GOERawMoments.matrixAbsoluteDet] using hLaw.integrable_fun_comp hR2.1
  have hBM : (∫ J,B J^2 ∂μ) ≤ bulkSecondMomentBound b g := by
    have hEq := hLaw.integral_comp
      (((matrixAbsoluteDet_measurable n k).div_const m).pow_const (2 : ℕ)).aestronglyMeasurable
    simp only [Function.comp_def] at hEq
    change (∫ J,B J^2 ∂μ)=_ at hEq
    rw [hEq]
    simpa only [Real.rpow_two, bulkSecondMomentBound, m, b, physicalMean, GOESharpMoments.matrixAbsoluteDet, GOERawMoments.matrixAbsoluteDet,
      show 4*b*(2:ℝ)^2/g^2=16*b/g^2 by ring] using hR2.2
  have hSchur := actual_common_clipped_schur_value_mse c hc hb (d := 4) (by omega) hdeg
    x y v hx hy hv hvtan e he htanx htany hve f h hh hr hδ hM hρ hA hinv w hw k
  have hκ : 0 < κ := mul_pos (scaleFactor_pos n hN hb) hρ
  have hSym (J : Disorder (n+3) P) : (hessianMatrix c x e J).IsHermitian := by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial,hessianMatrix] using hessianEntry_symm c x e j i J
  have hSpos : 0 < s := physicalSchurMultiplier_pos hb (by linarith)
  have hApprox := normalized_full_border_schur_error hκ (hessianMatrix c x e)
    (tensor_hessianMatrix_measurable c x e) hSym hLaw
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v))
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)
    hFull.1 s hFull.2.1 hB2
    (by simpa only [clippedSchur,actualClippedSchurFactor] using hSchur.1)
    (by change Measurable (actualClippedSchurFactor c x e v k κ); exact actualClippedSchurFactor_measurable c x e v k hκ)
  simp only [abs_of_pos hSpos] at hApprox
  have hMajor :
      Real.sqrt (∫ J,B J^2 ∂μ)*Real.sqrt E+
        (Real.sqrt (∫ J,D J^2 ∂μ)+s*Real.sqrt (∫ J,B J^2 ∂μ))*
          Real.sqrt ((goeLaw (n+1) (n+3) b).real (gapEvent n k κ)ᶜ) ≤
      Real.sqrt (bulkSecondMomentBound b g)*Real.sqrt E+
        (Real.sqrt (fullBorderSecondBound b g ρ Z (7*profileBound c*M/δ) (profileBound c*M/δ))+
          s*Real.sqrt (bulkSecondMomentBound b g))*
            Real.sqrt (Real.exp (-(n+1:ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2))) := by
    have hDM := hFull.2.2
    have hGM := hGapAll (n+3) (by omega) k hk
    gcongr
  refine ⟨hApprox.1,?_,?_⟩
  · exact hApprox.2.1.trans hMajor
  · exact hApprox.2.2.trans hMajor

end
end SlowEquilibration.SphericalCommonHessianRegression

