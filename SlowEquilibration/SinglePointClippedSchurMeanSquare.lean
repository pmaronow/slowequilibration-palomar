-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SinglePointSchurConcentration
public import SlowEquilibration.GOEPhysicalCovarianceSourceRate

/-! Source one-point Schur concentration at the true physical bulk law,
with no moment, covariance, independence, or concentration premises. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations GaussianObservationCoercivity GaussianQuadraticVariance
open GOEClippedResolvent GOEScaling CanonicalGOERealization BoundedQuadraticConvergence
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem actual_single_clipped_schur_mixed_mse {n P ℓ : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin (n+1) → Vector (n+3)) (he : Orthonormal ℝ e)
    (htan : ∀ i,inner ℝ (e i) x=0) (hve : ∀ i,inner ℝ (e i) v=0)
    (f : Fin ℓ → Vector (n+3)) (hA : Surjective (singleMixedObservation c x f))
    (w : MixedObservationSpace ℓ) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    let A:=singleMixedObservation c x f
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let L:=(Real.sqrt (b/3)*ρ)⁻¹
    let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
    Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
      (∫ J,F J^2 ∂coefficientKernel A w) ≤
        (4*b+32*b^2*L^2)/(n+3:ℕ)+
          4*(∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
            ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let A:=singleMixedObservation c x f
  let η:=coefficientKernel A w
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let T:=fun J=>clippedInverseOperator k κ (hessianMatrix c x e J)
  let Y:=actualObservation (commonRowCLM c x e v)
  let Q:=fun J=>inner ℝ (Y J) (T J (Y J))
  let G:=fun J=>Q J-(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap
  let R:=fun J=>Q J-b*physicalResolvent b k
  let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
  let C:=fun J=>-actualObservation (cornerCLM c x v) J
  have hN : 0 < n+3:=by omega
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n hN hb) hρ
  have hScale:=GOEPhysicalPrefactors.scaleFactor_lower n 2 hb.le
  simp only [show n+1+2=n+3 by omega,Nat.cast_ofNat,show (2+1:ℝ)=3 by norm_num] at hScale
  have hLowerPos : 0 < Real.sqrt (b/3)*ρ := by dsimp only [b];positivity
  have hSL (W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ‖clippedInverseOperator k κ W‖ ≤ L :=
    (clippedInverseOperator_norm_le k hκ W).trans
      (inv_anti₀ hLowerPos (mul_le_mul_of_nonneg_right hScale hρ.le))
  have hRow:=actual_single_row_mixed_bulk_operator_mse hN c hc hb hdeg x v hx hv hvtan e he htan hve f hA w
    (by positivity : 0 ≤ L) (clippedInverseOperator k κ) (clippedInverseOperator_measurable (n+1) k hκ)
    (fun W=>clippedInverseOperator_symmetric k κ W) hSL
  have hRowBound : (∫ J,G J^2 ∂η) ≤ 8*b^2*L^2/(n+3:ℕ) := by
    apply hRow.2.trans
    have hn : (n+1:ℝ) ≤ (n+3:ℕ) := by norm_cast;omega
    calc
      _ ≤ 8*(n+3:ℕ)*(b/(n+3:ℕ))^2*L^2 := by gcongr <;> norm_num
      _=_:=by field_simp
  let Φ:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
  have hΦ : Measurable Φ:=((physicalCovarianceTrace_measurable n 2 b k ρ).sub_const _).pow_const 2
  have hΦI : Integrable Φ (goeLaw (n+1) (n+3) b):=
    physicalCovarianceTrace_square_integrable n 2 hb hρ k (b*physicalResolvent b k)
  have hLaw:=single_common_matrix_mixed_hasLaw hN c hc hdeg x hx e he htan f w
  have hEq (J:Disorder (n+3) P) : (R J-G J)^2=Φ (hessianMatrix c x e J) := by
    dsimp only [R,G,Φ,Q,T]
    rw [physicalCovarianceTrace_eq_operator_trace n 2 hb.le k ρ]
    ring
  have hDiff : Integrable (fun J=>(R J-G J)^2) η := by
    simpa only [Function.comp_def,← hEq] using hLaw.integrable_comp (f:=Φ) hΦI
  have hTraceEq : (∫ J,(R J-G J)^2 ∂η) = ∫ W,Φ W ∂goeLaw (n+1) (n+3) b := by
    simpa only [Function.comp_def,← hEq] using hLaw.integral_comp hΦ.aestronglyMeasurable
  have hRM : Measurable R := by
    have hYM:=actual_linearObservation_measurable (commonRowCLM c x e v)
    have hTM:=(clippedInverseOperator_measurable (n+1) k hκ).comp (tensor_hessianMatrix_measurable c x e)
    have hEval : Measurable (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) :=
      (show Continuous (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) from by fun_prop).measurable
    exact (hYM.inner (hEval.comp (hTM.prodMk hYM))).sub_const _
  have hR:=integral_square_difference_bound η R G hRM hRow.1 hDiff
  have hRBound : (∫ J,R J^2 ∂η) ≤ 16*b^2*L^2/(n+3:ℕ)+2*(∫ W,Φ W ∂goeLaw (n+1) (n+3) b) := by
    rw [hTraceEq] at hR
    refine hR.2.trans ?_
    convert add_le_add (mul_le_mul_of_nonneg_left hRowBound (by norm_num : (0:ℝ)≤2)) le_rfl using 1 <;> ring
  have hCorner:=actual_conditional_corner_second_moment hN c hc x hx v hv hvtan A hA w
  have hMean : cornerCLM c x v (lift A w)=0 := lift_map_eq_zero_of_cross_zero A _
    (single_corner_mixed_cross_zero hN c hc hdeg x v hvtan f) w
  simp only [hMean,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] at hCorner
  have hCI : Integrable (fun J=>C J^2) η := by simpa only [C,neg_sq] using hCorner.1
  have hFG (J) : (F J-C J)^2=R J^2 := by
    dsimp only [F,C,R,Q,T,Y,actualClippedSchurFactor,physicalSchurMultiplier]
    ring
  have hFM : Measurable F:=(actualClippedSchurFactor_measurable c x e v k hκ).sub_const _
  have hFinal:=integral_square_difference_bound η F C hFM hCI (by simpa only [hFG] using hR.1)
  simp only [hFG] at hFinal
  refine ⟨hFinal.1,hFinal.2.trans ?_⟩
  have hcB : (∫ J,C J^2 ∂η) ≤ 2*b/(n+3:ℕ) := by simpa only [C,neg_sq] using hCorner.2
  calc
    _ ≤ 2*(2*b/(n+3:ℕ))+2*(16*b^2*L^2/(n+3:ℕ)+2*(∫ W,Φ W ∂goeLaw (n+1) (n+3) b)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcB (by norm_num))
        (mul_le_mul_of_nonneg_left hRBound (by norm_num))
    _=_:=by dsimp only [b,L,Φ];ring

theorem actual_single_clipped_schur_mixed_L2_rate {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    {g ρ : ℝ} (hg : 0 < g) (hρ : 0 < ρ)
    (hρg : ρ ≤ (g/Real.sqrt (secondCovariance c 1))/2) :
    ∃ K:ℝ,0 < K ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x v : Vector (n+3)) (_hx : ‖x‖^2=(n+3:ℕ)) (_hv : ‖v‖=1) (_hvtan : inner ℝ v x=0)
      (e : Fin (n+1) → Vector (n+3)) (_he : Orthonormal ℝ e)
      (_htan : ∀ i,inner ℝ (e i) x=0) (_hve : ∀ i,inner ℝ (e i) v=0)
      (f : Fin ℓ → Vector (n+3)) (_hA : Surjective (singleMixedObservation c x f))
      (w : MixedObservationSpace ℓ) (k : ℝ),2*Real.sqrt (secondCovariance c 1)+g ≤ k →
      let A:=singleMixedObservation c x f
      let b:=secondCovariance c 1
      let κ:=scaleFactor n (n+3) b*ρ
      let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
      Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
        (∫ J,F J^2 ∂coefficientKernel A w) ≤ K/(n+3:ℕ) := by
  let b:=secondCovariance c 1
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  obtain ⟨T,hT,hRate⟩:=physical_covariance_trace_source_L2_rate 2 hb hg hρ hρg
  refine ⟨4*b+32*b^2*L^2+4*T,by dsimp only [b];positivity,?_⟩
  filter_upwards [hRate] with n hn
  intro ℓ x v hx hv hvtan e he htan hve f hA w k hk
  dsimp only
  have hh:=actual_single_clipped_schur_mixed_mse c hc hb hdeg x v hx hv hvtan e he htan hve f hA w k hρ
  have hTrace:=hn k hk
  simp only [show n+1+2=n+3 by omega] at hTrace
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ (4*b+32*b^2*L^2)/(n+3:ℕ)+4*(T/(n+3:ℕ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hTrace (by norm_num))
    _=_:=by ring

theorem actual_single_clipped_schur_value_mse {n P ℓ : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin (n+1) → Vector (n+3)) (he : Orthonormal ℝ e)
    (htan : ∀ i,inner ℝ (e i) x=0) (hve : ∀ i,inner ℝ (e i) v=0)
    (f : Fin ℓ → Vector (n+3)) (hA : Surjective (singleValueObservation c x f))
    (w : ValueObservationSpace ℓ) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    let A:=singleValueObservation c x f
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let L:=(Real.sqrt (b/3)*ρ)⁻¹
    let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
    Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
      (∫ J,F J^2 ∂coefficientKernel A w) ≤
        (4*b+32*b^2*L^2)/(n+3:ℕ)+
          4*(∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
            ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let A:=singleValueObservation c x f
  let η:=coefficientKernel A w
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let T:=fun J=>clippedInverseOperator k κ (hessianMatrix c x e J)
  let Y:=actualObservation (commonRowCLM c x e v)
  let Q:=fun J=>inner ℝ (Y J) (T J (Y J))
  let G:=fun J=>Q J-(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap
  let R:=fun J=>Q J-b*physicalResolvent b k
  let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
  let C:=fun J=>-actualObservation (cornerCLM c x v) J
  have hN : 0 < n+3:=by omega
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n hN hb) hρ
  have hScale:=GOEPhysicalPrefactors.scaleFactor_lower n 2 hb.le
  simp only [show n+1+2=n+3 by omega,Nat.cast_ofNat,show (2+1:ℝ)=3 by norm_num] at hScale
  have hLowerPos : 0 < Real.sqrt (b/3)*ρ := by dsimp only [b];positivity
  have hSL (W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ‖clippedInverseOperator k κ W‖ ≤ L :=
    (clippedInverseOperator_norm_le k hκ W).trans
      (inv_anti₀ hLowerPos (mul_le_mul_of_nonneg_right hScale hρ.le))
  have hRow:=actual_single_row_value_bulk_operator_mse hN c hc hb hdeg x v hx hv hvtan e he htan hve f hA w
    (by positivity : 0 ≤ L) (clippedInverseOperator k κ) (clippedInverseOperator_measurable (n+1) k hκ)
    (fun W=>clippedInverseOperator_symmetric k κ W) hSL
  have hRowBound : (∫ J,G J^2 ∂η) ≤ 8*b^2*L^2/(n+3:ℕ) := by
    apply hRow.2.trans
    have hn : (n+1:ℝ) ≤ (n+3:ℕ) := by norm_cast;omega
    calc
      _ ≤ 8*(n+3:ℕ)*(b/(n+3:ℕ))^2*L^2 := by gcongr <;> norm_num
      _=_:=by field_simp
  let Φ:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
  have hΦ : Measurable Φ:=((physicalCovarianceTrace_measurable n 2 b k ρ).sub_const _).pow_const 2
  have hΦI : Integrable Φ (goeLaw (n+1) (n+3) b):=
    physicalCovarianceTrace_square_integrable n 2 hb hρ k (b*physicalResolvent b k)
  have hLaw:=single_common_matrix_value_hasLaw hN c hc hdeg x hx e he htan f w
  have hEq (J:Disorder (n+3) P) : (R J-G J)^2=Φ (hessianMatrix c x e J) := by
    dsimp only [R,G,Φ,Q,T]
    rw [physicalCovarianceTrace_eq_operator_trace n 2 hb.le k ρ]
    ring
  have hDiff : Integrable (fun J=>(R J-G J)^2) η := by
    simpa only [Function.comp_def,← hEq] using hLaw.integrable_comp (f:=Φ) hΦI
  have hTraceEq : (∫ J,(R J-G J)^2 ∂η) = ∫ W,Φ W ∂goeLaw (n+1) (n+3) b := by
    simpa only [Function.comp_def,← hEq] using hLaw.integral_comp hΦ.aestronglyMeasurable
  have hRM : Measurable R := by
    have hYM:=actual_linearObservation_measurable (commonRowCLM c x e v)
    have hTM:=(clippedInverseOperator_measurable (n+1) k hκ).comp (tensor_hessianMatrix_measurable c x e)
    have hEval : Measurable (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) :=
      (show Continuous (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) from by fun_prop).measurable
    exact (hYM.inner (hEval.comp (hTM.prodMk hYM))).sub_const _
  have hR:=integral_square_difference_bound η R G hRM hRow.1 hDiff
  have hRBound : (∫ J,R J^2 ∂η) ≤ 16*b^2*L^2/(n+3:ℕ)+2*(∫ W,Φ W ∂goeLaw (n+1) (n+3) b) := by
    rw [hTraceEq] at hR
    refine hR.2.trans ?_
    convert add_le_add (mul_le_mul_of_nonneg_left hRowBound (by norm_num : (0:ℝ)≤2)) le_rfl using 1 <;> ring
  have hCorner:=actual_conditional_corner_second_moment hN c hc x hx v hv hvtan A hA w
  have hMean : cornerCLM c x v (lift A w)=0 := lift_map_eq_zero_of_cross_zero A _
    (single_corner_value_cross_zero hN c hc hdeg x v hvtan f) w
  simp only [hMean,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] at hCorner
  have hCI : Integrable (fun J=>C J^2) η := by simpa only [C,neg_sq] using hCorner.1
  have hFG (J) : (F J-C J)^2=R J^2 := by
    dsimp only [F,C,R,Q,T,Y,actualClippedSchurFactor,physicalSchurMultiplier]
    ring
  have hFM : Measurable F:=(actualClippedSchurFactor_measurable c x e v k hκ).sub_const _
  have hFinal:=integral_square_difference_bound η F C hFM hCI (by simpa only [hFG] using hR.1)
  simp only [hFG] at hFinal
  refine ⟨hFinal.1,hFinal.2.trans ?_⟩
  have hcB : (∫ J,C J^2 ∂η) ≤ 2*b/(n+3:ℕ) := by simpa only [C,neg_sq] using hCorner.2
  calc
    _ ≤ 2*(2*b/(n+3:ℕ))+2*(16*b^2*L^2/(n+3:ℕ)+2*(∫ W,Φ W ∂goeLaw (n+1) (n+3) b)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcB (by norm_num))
        (mul_le_mul_of_nonneg_left hRBound (by norm_num))
    _=_:=by dsimp only [b,L,Φ];ring

theorem actual_single_clipped_schur_value_L2_rate {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    {g ρ : ℝ} (hg : 0 < g) (hρ : 0 < ρ)
    (hρg : ρ ≤ (g/Real.sqrt (secondCovariance c 1))/2) :
    ∃ K:ℝ,0 < K ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x v : Vector (n+3)) (_hx : ‖x‖^2=(n+3:ℕ)) (_hv : ‖v‖=1) (_hvtan : inner ℝ v x=0)
      (e : Fin (n+1) → Vector (n+3)) (_he : Orthonormal ℝ e)
      (_htan : ∀ i,inner ℝ (e i) x=0) (_hve : ∀ i,inner ℝ (e i) v=0)
      (f : Fin ℓ → Vector (n+3)) (_hA : Surjective (singleValueObservation c x f))
      (w : ValueObservationSpace ℓ) (k : ℝ),2*Real.sqrt (secondCovariance c 1)+g ≤ k →
      let A:=singleValueObservation c x f
      let b:=secondCovariance c 1
      let κ:=scaleFactor n (n+3) b*ρ
      let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
      Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
        (∫ J,F J^2 ∂coefficientKernel A w) ≤ K/(n+3:ℕ) := by
  let b:=secondCovariance c 1
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  obtain ⟨T,hT,hRate⟩:=physical_covariance_trace_source_L2_rate 2 hb hg hρ hρg
  refine ⟨4*b+32*b^2*L^2+4*T,by dsimp only [b];positivity,?_⟩
  filter_upwards [hRate] with n hn
  intro ℓ x v hx hv hvtan e he htan hve f hA w k hk
  dsimp only
  have hh:=actual_single_clipped_schur_value_mse c hc hb hdeg x v hx hv hvtan e he htan hve f hA w k hρ
  have hTrace:=hn k hk
  simp only [show n+1+2=n+3 by omega] at hTrace
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ (4*b+32*b^2*L^2)/(n+3:ℕ)+4*(T/(n+3:ℕ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hTrace (by norm_num))
    _=_:=by ring

end
end SlowEquilibration.SphericalCommonHessianRegression
