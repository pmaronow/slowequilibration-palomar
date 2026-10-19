-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalCommonBorderIntegerMoments
public import SlowEquilibration.CommonHessianActualRowMoments
public import SlowEquilibration.CommonHessianActualCornerMoments
public import SlowEquilibration.SphericalPosteriorCommonMarginal
public import SlowEquilibration.SphericalLinearObservationMeasurable
public import SlowEquilibration.GOEPhysicalPrefactors

/-! Full original-posterior border integer moments from the actual tensor
row/corner covariance and their actual regression mean. The model consumers
derive every moment and marginal law; none is an estimate premise.
-/
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

def cornerIntegerBound (r : ℕ) (b Dc : ℝ) : ℝ :=
  (2 : ℝ)^(2*r)*((Nat.factorial (2*r) : ℝ)*Real.exp (Real.sqrt (2*b)+b)+Dc^(2*r))

def rowIntegerBound (r : ℕ) (b D : ℝ) : ℝ :=
  (2 : ℝ)^(4*r)*((Nat.factorial (4*r) : ℝ)*Real.exp (Real.sqrt b+b/2)+D^(4*r))

def fullBorderIntegerBound (r : ℕ) (b g ρ Z Dc D : ℝ) : ℝ :=
  Real.sqrt ((2 : ℝ)^(2*r)*Real.exp (4*b*(2*r)^2/g^2)) *
    Real.sqrt ((2:ℝ)^(4*r)*(Z^(2*r)+cornerIntegerBound r b Dc)+
      (2:ℝ)^(2*r)*((Real.sqrt (b/3)*ρ)⁻¹)^(2*r)*rowIntegerBound r b D)

/-- A true actual marginal law and actual regression means suffice for the
full original coefficient-kernel border integer moment. Ordinary moment
hypotheses are discharged by the model covariance identities.
-/
theorem actual_common_border_integer_moment_from_regression_eventually (r : ℕ) (hrPos : 1 ≤ r) {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    {g ρ Z : ℝ} (hg : 0 < g) (hρ : 0 < ρ)
    (hρg : ρ ≤ g/(2*Real.sqrt (secondCovariance c 1))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F],
      ∀ (x : Vector (n+3)), ‖x‖^2=(n+3:ℕ) →
      ∀ (e : Fin (n+1) → Vector (n+3)), Orthonormal ℝ e →
        (∀ i,inner ℝ (e i) x=0) →
      ∀ v : Vector (n+3), ‖v‖=1 → inner ℝ v x=0 → (∀ i,inner ℝ (e i) v=0) →
      ∀ (A : EuclideanDisorder (n+3) P →L[ℝ] F), Surjective A →
      ∀ w : F,
      HasLaw (hessianMatrix c x e) (goeLaw (n+1) (n+3) (secondCovariance c 1)) (coefficientKernel A w) →
      ∀ k : ℝ, 2*Real.sqrt (secondCovariance c 1)+g ≤ k → k ≤ Z →
      ∀ Dc D : ℝ, ‖cornerCLM c x v (lift A w)‖ ≤ Dc →
        ‖commonRowCLM c x e v (lift A w)‖ ≤ D →
      0 < physicalMean n (n+3) (secondCovariance c 1) k ∧
      Integrable (fun J => (fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^r) (coefficientKernel A w) ∧
      (∫ J,(fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^r ∂coefficientKernel A w) ≤
          fullBorderIntegerBound r (secondCovariance c 1) g ρ Z Dc D := by
  filter_upwards [full_border_integer_moment_eventually r hrPos hb hg hρ hρg] with n hall
  intro F _ _ _ _ _ x hx e he htan v hv hvtan hve A hA w hLaw k hk hkZ Dc D hCornerMean hRowMean
  let b := secondCovariance c 1
  have hN : 0 < n+3 := by omega
  have hC := conditional_corner_norm_moments hN c hc hb x hx v hv hvtan A hA (2*r)
  have hR := conditional_common_row_norm_moments hN (by omega : n+1 ≤ n+3)
    c hc hb x hx e he htan v hv hvtan hve A hA (4*r)
  have hCM := coefficientKernel_norm_moment_of_centered_moment A (cornerCLM c x v) w (2*r)
    hC.1 hC.2 hCornerMean
  have hRM := coefficientKernel_norm_moment_of_centered_moment A (commonRowCLM c x e v) w (4*r)
    hR.1 hR.2 hRowMean
  have hScale := GOEPhysicalPrefactors.scaleFactor_lower n 2 hb.le
  simp only [show n+1+2=n+3 by omega, Nat.cast_ofNat, show (2+1 : ℝ)=3 by norm_num] at hScale
  have hLower : Real.sqrt (b/3)*ρ ≤ scaleFactor n (n+3) b*ρ :=
    mul_le_mul_of_nonneg_right hScale hρ.le
  have hLowerPos : 0 < Real.sqrt (b/3)*ρ := by dsimp only [b]; positivity
  have hCut : (scaleFactor n (n+3) b*ρ)⁻¹ ≤ (Real.sqrt (b/3)*ρ)⁻¹ :=
    inv_anti₀ hLowerPos hLower
  have hSym (J : Disorder (n+3) P) : (hessianMatrix c x e J).IsHermitian := by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial,hessianMatrix] using hessianEntry_symm c x e j i J
  have hFull := hall (n+3) (by omega) k hk (Disorder (n+3) P) (coefficientKernel A w)
    (hessianMatrix c x e) (tensor_hessianMatrix_measurable c x e) hLaw hSym
    (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v))
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)
    ((Real.sqrt (b/3)*ρ)⁻¹) (cornerIntegerBound r b Dc) (rowIntegerBound r b D) hCut
    (by simpa only [Real.norm_eq_abs] using hCM.1) hRM.1
    (by simpa only [cornerIntegerBound,b,Real.norm_eq_abs] using hCM.2)
    (by simpa only [rowIntegerBound,b] using hRM.2)
  refine ⟨hFull.1,hFull.2.1,hFull.2.2.trans ?_⟩
  have hk0 : 0 ≤ k := by linarith [Real.sqrt_nonneg b]
  have hkAbs : |k| ≤ Z := by simpa only [abs_of_nonneg hk0] using hkZ
  unfold fullBorderIntegerBound
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (pow_le_pow_left₀ (abs_nonneg k) hkAbs (2*r)) le_rfl) (by norm_num))
    le_rfl


/-- Genuine mixed-pair posterior full border moments, with all covariance,
marginal-law and moment estimates derived internally at every target. -/
theorem actual_common_border_mixed_integer_moment_eventually (r : ℕ) (hrPos : 1 ≤ r) {P : ℕ}
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
        physicalMean n (n+3) (secondCovariance c 1) k)^r) (coefficientKernel A w) ∧
      (∫ J,(fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^r ∂coefficientKernel A w) ≤
          fullBorderIntegerBound r (secondCovariance c 1) g ρ Z
            (7*profileBound c*M/δ) (profileBound c*M/δ) := by
  filter_upwards [actual_common_border_integer_moment_from_regression_eventually r hrPos (Z := Z) c hc hb hg hρ hρg] with n hall
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  dsimp only
  have hN : 0 < n+3 := by omega
  have h3 : ∀ p,c p≠0 → 3 ≤ p.val.val := fun p hp => (by omega : 3 ≤ 4).trans (hdeg p hp)
  have hLaw := posterior_common_matrix_mixed_hasLaw hN c hc h3 x y hx e he htanx htany f h w
  have hCM := mixed_lift_hessian_bound hN c hc hdeg x y v v hx hy hv hv hvtan hvtan f h hh w hδ hM hinv hw hr
  have hDc0 : 0 ≤ 7*profileBound c*M/δ := by positivity [profileBound_pos c]
  have hD0 : 0 ≤ profileBound c*M/δ := by positivity [profileBound_pos c]
  have hCMean : ‖cornerCLM c x v (lift (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)) w)‖ ≤
      7*profileBound c*M/δ := by
    rw [Real.norm_eq_abs,cornerCLM]
    exact hCM.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hDc0)
  have hRM := common_row_pair_mixed_lift_norm hN c hc (d := 4) (by omega) hdeg x y v hy hv hvtan e he
    htanx htany f h hh hr hδ hM hinv w hw
  have hRMean : ‖commonRowCLM c x e v (lift (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y h)) w)‖ ≤
      profileBound c*M/δ := by
    have hp : |overlap x y|^(4-2) ≤ (1 : ℝ) := by
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) hr (4-2)
    exact hRM.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hD0)
  exact hall (WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ)) x hx e he htanx v hv hvtan hve _ hA w hLaw k hk hkZ _ _ hCMean hRMean

/-- Genuine value-pair posterior full border moments, with all covariance,
marginal-law and moment estimates derived internally at every target. -/
theorem actual_common_border_value_integer_moment_eventually (r : ℕ) (hrPos : 1 ≤ r) {P : ℕ}
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
        physicalMean n (n+3) (secondCovariance c 1) k)^r) (coefficientKernel A w) ∧
      (∫ J,(fullBorder (hessianMatrix c x e) k
        (actualObservation (cornerCLM c x v)) (actualObservation (commonRowCLM c x e v)) J/
        physicalMean n (n+3) (secondCovariance c 1) k)^r ∂coefficientKernel A w) ≤
          fullBorderIntegerBound r (secondCovariance c 1) g ρ Z
            (7*profileBound c*M/δ) (profileBound c*M/δ) := by
  filter_upwards [actual_common_border_integer_moment_from_regression_eventually r hrPos (Z := Z) c hc hb hg hρ hρg] with n hall
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f h hh hr hA hinv w hw k hk hkZ
  dsimp only
  have hN : 0 < n+3 := by omega
  have h3 : ∀ p,c p≠0 → 3 ≤ p.val.val := fun p hp => (by omega : 3 ≤ 4).trans (hdeg p hp)
  have hLaw := posterior_common_matrix_value_hasLaw hN c hc h3 x y hx e he htanx htany f h w
  have hCM := value_lift_hessian_bound hN c hc hdeg x y v v hx hy hv hv hvtan hvtan f h hh w hδ hM hinv hw hr
  have hDc0 : 0 ≤ 7*profileBound c*M/δ := by positivity [profileBound_pos c]
  have hD0 : 0 ≤ profileBound c*M/δ := by positivity [profileBound_pos c]
  have hCMean : ‖cornerCLM c x v (lift (pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)) w)‖ ≤
      7*profileBound c*M/δ := by
    rw [Real.norm_eq_abs,cornerCLM]
    exact hCM.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hDc0)
  have hRM := common_row_pair_value_lift_norm hN c hc (d := 4) (by omega) hdeg x y v hy hv hvtan e he
    htanx htany f h hh hr hδ hM hinv w hw
  have hRMean : ‖commonRowCLM c x e v (lift (pairHilbert (singleValueObservation c x f) (singleValueObservation c y h)) w)‖ ≤
      profileBound c*M/δ := by
    have hp : |overlap x y|^(4-2) ≤ (1 : ℝ) := by
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) hr (4-2)
    exact hRM.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hD0)
  exact hall (WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ)) x hx e he htanx v hv hvtan hve _ hA w hLaw k hk hkZ _ _ hCMean hRMean

end
end SlowEquilibration.SphericalCommonHessianRegression

