module
public import QuantitativePaper.VectorShiftEnergy

@[expose] public section

/-! Genuine measurability and uniform boundedness of the spin/Hessian energy. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem contDiff_vectorMagnetization_joint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : VectorParameter n => vectorMagnetization s β t p.1 j p.2) :=
  contDiff_piLp' 2 (fun i => (boundedJets_vectorMagnetization_component s β t j i).1)

theorem norm_vectorMagnetization_le_sqrt {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    ‖vectorMagnetization s β t p j x‖ ≤ Real.sqrt (n : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _ : Fin n,(1 : ℝ) := Finset.sum_le_sum fun i _ => by
      have hb := vectorMagnetization_component_bound s β t p j x i
      rw [Real.norm_eq_abs,sq_abs]
      have hab := abs_le.mp hb
      nlinarith [sq_nonneg (vectorMagnetization s β t p j x i)]
    _ = _ := by simp

theorem vectorFieldHessian_quadratic_eq_joint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : VectorParameter n) (j : ℕ) (w : Field n) :
    inner ℝ w (vectorFieldHessian s β t p.1 j p.2 w)=
      directionalHessian (fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2) p (0,w) := by
  let F := fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2
  have he : (fun r : ℝ => F (p+r • ((0,w) : VectorParameter n)))=
      fun r => vectorRecursion s β t p.1 j (p.2+r • w) := by
    funext r
    simp [F,Prod.smul_mk]
  rw [real_inner_comm,vectorFieldHessian,inner_hessianOperator]
  change directionalHessian (vectorRecursion s β t p.1 j) p.2 w=directionalHessian F p (0,w)
  rw [directionalHessian_eq_secondDeriv_line _
    ((contDiff_vectorRecursion_field s β t p.1 j).of_le (by simp)),
    directionalHessian_eq_secondDeriv_line F
      ((contDiff_vectorRecursion_joint s β t j).of_le (by simp)),he]

theorem vectorFieldHessian_bilinear_eq_joint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : VectorParameter n) (j : ℕ) (u v : Field n) :
    inner ℝ (vectorFieldHessian s β t p.1 j p.2 u) v=
      fderiv ℝ (fderiv ℝ (fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2)) p
        (0,u) (0,v) := by
  let B := fderiv ℝ (fderiv ℝ (vectorRecursion s β t p.1 j)) p.2
  let C := fderiv ℝ (fderiv ℝ (fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2)) p
  have hB : B u v=B v u :=
    ((contDiff_vectorRecursion_field s β t p.1 j).contDiffAt.isSymmSndFDerivAt (by simp)).eq u v
  have hC : C (0,u) (0,v)=C (0,v) (0,u) :=
    ((contDiff_vectorRecursion_joint s β t j).contDiffAt.isSymmSndFDerivAt (by simp)).eq (0,u) (0,v)
  have hq (w : Field n) : B w w=C (0,w) (0,w) := by
    have hh := vectorFieldHessian_quadratic_eq_joint s β t p j w
    rw [real_inner_comm,vectorFieldHessian,inner_hessianOperator] at hh
    exact hh
  have hs := hq (u+v)
  have he : ((0,u+v) : VectorParameter n)=((0,u) : VectorParameter n)+(0,v) := by simp
  rw [he] at hs
  simp only [map_add,add_apply] at hs
  rw [vectorFieldHessian,inner_hessianOperator]
  change B u v=C (0,u) (0,v)
  linarith [hq u,hq v]

theorem vectorFieldHessian_component_eq_joint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : VectorParameter n) (j : ℕ) (i l : Fin n) :
    (vectorFieldHessian s β t p.1 j p.2 (EuclideanSpace.single i 1)) l=
      fderiv ℝ (fderiv ℝ (fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2)) p
        (vectorJointCoordinateDirection n i) (vectorJointCoordinateDirection n l) := by
  simpa [vectorJointCoordinateDirection,EuclideanSpace.inner_single_right] using
    vectorFieldHessian_bilinear_eq_joint s β t p j (EuclideanSpace.single i 1) (EuclideanSpace.single l 1)

theorem continuous_vectorFieldHessian_component {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) (i l : Fin n) :
    Continuous (fun p : VectorParameter n =>
      (vectorFieldHessian s β t p.1 j p.2 (EuclideanSpace.single i 1)) l) := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2)) :=
    (contDiff_vectorRecursion_joint s β t j).fderiv_right (by simp)
  have h₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2))) :=
    h₁.fderiv_right (by simp)
  have he := funext fun p : VectorParameter n => vectorFieldHessian_component_eq_joint s β t p j i l
  rw [he]
  exact (h₂.continuous.clm_apply continuous_const).clm_apply continuous_const

theorem exists_vectorFieldHessian_component_bound {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) : ∃ K : ℝ,0 ≤ K ∧ ∀ (p : VectorParameter n) (i l : Fin n),
      |(vectorFieldHessian s β t p.1 j p.2 (EuclideanSpace.single i 1)) l| ≤ K := by
  obtain ⟨K,hK,hBound⟩ := (boundedPositiveJets_vectorRecursion_joint (n := n) s β t j).2 2 (by omega)
  refine ⟨K,hK,fun p i l => ?_⟩
  rw [vectorFieldHessian_component_eq_joint]
  let C := fderiv ℝ (fderiv ℝ (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2)) p
  have hh := ((C (vectorJointCoordinateDirection n i)).le_opNorm (vectorJointCoordinateDirection n l)).trans
    (mul_le_mul_of_nonneg_right (C.le_opNorm (vectorJointCoordinateDirection n i)) (norm_nonneg _))
  have hi : ‖vectorJointCoordinateDirection n i‖=1 := by simp [vectorJointCoordinateDirection,Prod.norm_def]
  have hl : ‖vectorJointCoordinateDirection n l‖=1 := by simp [vectorJointCoordinateDirection,Prod.norm_def]
  rw [hi,hl,mul_one,mul_one] at hh
  rw [Real.norm_eq_abs] at hh
  apply hh.trans
  dsimp [C]
  rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact hBound p

def vectorSpinHessianEnergy {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) (σ : Configuration n) (p : VectorParameter n) : ℝ :=
  inner ℝ (spinVector σ-vectorMagnetization s β t p.1 j p.2)
    (vectorFieldHessian s β t p.1 j p.2 (spinVector σ-vectorMagnetization s β t p.1 j p.2))

theorem continuous_vectorSpinHessianEnergy {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) (σ : Configuration n) :
    Continuous (vectorSpinHessianEnergy (n := n) s β t j σ) := by
  let F := fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2
  let D := fun y : VectorParameter n => ((0,spinVector σ-vectorMagnetization s β t y.1 j y.2) : VectorParameter n)
  have hd : Continuous D := continuous_const.prodMk
    (continuous_const.sub (contDiff_vectorMagnetization_joint s β t j).continuous)
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ F) :=
    (contDiff_vectorRecursion_joint s β t j).fderiv_right (by simp)
  have hc : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ F)) := h₁.fderiv_right (by simp)
  have he : vectorSpinHessianEnergy (n := n) s β t j σ=fun y => fderiv ℝ (fderiv ℝ F) y (D y) (D y) := by
    funext y
    exact vectorFieldHessian_quadratic_eq_joint s β t y j _
  rw [he]
  exact (hc.continuous.clm_apply hd).clm_apply hd

theorem exists_vectorSpinHessianEnergy_bound {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ (σ : Configuration n) (p : VectorParameter n),
      |vectorSpinHessianEnergy s β t j σ p| ≤ B := by
  obtain ⟨K,hK,hB⟩ := (boundedPositiveJets_vectorRecursion_joint (n := n) s β t j).2 2 (by omega)
  refine ⟨K*(2*Real.sqrt (n : ℝ))^2,mul_nonneg hK (sq_nonneg _),fun σ p => ?_⟩
  let F := fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2
  let D : VectorParameter n := (0,spinVector σ-vectorMagnetization s β t p.1 j p.2)
  have hn : ‖D‖ ≤ 2*Real.sqrt (n : ℝ) := by
    change max ‖(0 : Couplings n × ℝ)‖ ‖spinVector σ-vectorMagnetization s β t p.1 j p.2‖ ≤ _
    rw [norm_zero,max_eq_right (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by
      rw [norm_spinVector]
      have hb := norm_vectorMagnetization_le_sqrt s β t p.1 j p.2
      linarith)
  unfold vectorSpinHessianEnergy
  rw [vectorFieldHessian_quadratic_eq_joint]
  change |fderiv ℝ (fderiv ℝ F) p D D| ≤ _
  have hh := ((fderiv ℝ (fderiv ℝ F) p D).le_opNorm D).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ F) p).le_opNorm D) (norm_nonneg _))
  rw [←norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at hh
  rw [Real.norm_eq_abs] at hh
  have hnorm : ‖iteratedFDeriv ℝ 2 F p‖ ≤ K := hB p
  have hs : ‖D‖^2 ≤ (2*Real.sqrt (n : ℝ))^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 F p),norm_nonneg D]

end QuantitativePaper
