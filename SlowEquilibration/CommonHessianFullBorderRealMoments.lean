-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianFullBorderIntegerMoments
public import SlowEquilibration.NonnegativeRealMoment

/-! Every fixed real moment of the literal original-posterior full border.
The order and uniform constants are fixed before dimension and all targets. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression GaussianRegressionCovariance
open NormalizedPairObservations GaussianObservationCoercivity SphericalConditionalMatrices
open PhysicalCommonBorderMoments GOEPhysicalPotential GOEScaling PairHessianMean PairObservationNormBounds
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- Genuine mixed-pair posterior full border moments, with all covariance,
marginal-law and moment estimates derived internally at every target. -/
theorem actual_common_border_mixed_real_moment_eventually (q : ℝ) (hq : 1 ≤ q) {P : ℕ}
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
      0 < physicalMean n (n+3) (secondCovariance c 1) k ∧
      Integrable (fun J => (fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^q) (coefficientKernel A w) ∧
      (∫ J,(fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^q ∂coefficientKernel A w) ≤
          1+fullBorderIntegerBound (Nat.ceil q) (secondCovariance c 1) g ρ Z
            (7*profileBound c*M/δ) (profileBound c*M/δ) := by
  have hqr : q ≤ (Nat.ceil q:ℝ) := Nat.le_ceil q
  have hrPos : 1 ≤ Nat.ceil q := by exact_mod_cast hq.trans hqr
  filter_upwards [actual_common_border_mixed_integer_moment_eventually (Nat.ceil q) hrPos
    (Z := Z) c hc hb hdeg hg hρ hρg hδ hM] with n hall
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  dsimp only
  let A := pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)
  let D := fun J:Disorder (n+3) P=>fullBorder (hessianMatrix c x e) k
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
      physicalMean n (n+3) (secondCovariance c 1) k
  have hFull := hall ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  have hD : Measurable D := (fullBorder_measurable (tensor_hessianMatrix_measurable c x e) k
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)).div_const _
  have hD0 (J) : 0 ≤ D J := div_nonneg (abs_nonneg _) hFull.1.le
  have hReal := NonnegativeRealMoment.real_moment_of_integer (coefficientKernel A w) D hD hD0
    (by linarith : 0 ≤ q) (Nat.ceil q) hqr hFull.2.1
  exact ⟨hFull.1,hReal.1,hReal.2.trans (add_le_add le_rfl hFull.2.2)⟩

/-- Genuine value-pair posterior full border moments, with all covariance,
marginal-law and moment estimates derived internally at every target. -/
theorem actual_common_border_value_real_moment_eventually (q : ℝ) (hq : 1 ≤ q) {P : ℕ}
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
      0 < physicalMean n (n+3) (secondCovariance c 1) k ∧
      Integrable (fun J => (fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^q) (coefficientKernel A w) ∧
      (∫ J,(fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^q ∂coefficientKernel A w) ≤
          1+fullBorderIntegerBound (Nat.ceil q) (secondCovariance c 1) g ρ Z
            (7*profileBound c*M/δ) (profileBound c*M/δ) := by
  have hqr : q ≤ (Nat.ceil q:ℝ) := Nat.le_ceil q
  have hrPos : 1 ≤ Nat.ceil q := by exact_mod_cast hq.trans hqr
  filter_upwards [actual_common_border_value_integer_moment_eventually (Nat.ceil q) hrPos
    (Z := Z) c hc hb hdeg hg hρ hρg hδ hM] with n hall
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  dsimp only
  let A := pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)
  let D := fun J:Disorder (n+3) P=>fullBorder (hessianMatrix c x e) k
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
      physicalMean n (n+3) (secondCovariance c 1) k
  have hFull := hall ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  have hD : Measurable D := (fullBorder_measurable (tensor_hessianMatrix_measurable c x e) k
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)).div_const _
  have hD0 (J) : 0 ≤ D J := div_nonneg (abs_nonneg _) hFull.1.le
  have hReal := NonnegativeRealMoment.real_moment_of_integer (coefficientKernel A w) D hD hD0
    (by linarith : 0 ≤ q) (Nat.ceil q) hqr hFull.2.1
  exact ⟨hFull.1,hReal.1,hReal.2.trans (add_le_add le_rfl hFull.2.2)⟩

end
end SlowEquilibration.SphericalCommonHessianRegression
