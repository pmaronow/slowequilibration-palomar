module
public import QuantitativePaper.VectorFieldConditionalVariance
public import Targets.CoupledCascadeVariance

@[expose] public section

/-! Actual finite-dimensional Gaussian variance differentiation for the
constructed vector recursion. All growth and spatial derivative hypotheses
of the genuine Gaussian heat theorem are discharged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem hasDerivAt_vectorRecursion_field_gradient {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x w : Field n) (r : ℝ) :
    HasDerivAt (fun a : ℝ => vectorRecursion s β t p j (x+a • w))
      (inner ℝ (vectorMagnetization s β t p j (x+r • w)) w) r := by
  let F := fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2
  have hd := hasDerivAt_on_affine_line F
    ((contDiff_vectorRecursion_joint s β t j).of_le (by simp)) (p,x) (0,w) r
  have he : (fun a : ℝ => F ((p,x)+a • ((0,w) : VectorParameter n)))=
      fun a : ℝ => vectorRecursion s β t p j (x+a • w) := by
    funext a
    simp [F,Prod.smul_mk]
  rw [he] at hd
  have hh := fderiv_vectorRecursion_field s β t j
    ((p,x)+r • ((0,w) : VectorParameter n)) w
  simpa only [F,Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero] using hd.congr_deriv hh

theorem fderiv_vectorRecursion_coordinate {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    fderiv ℝ (vectorRecursion s β t p j) x (EuclideanSpace.single i (1 : ℝ))=
      vectorMagnetization s β t p j x i := by
  have h := (hasDerivAt_on_affine_line (vectorRecursion s β t p j)
    ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)) x
    (EuclideanSpace.single i (1 : ℝ)) 0).unique (hasDerivAt_vectorRecursion_coordinate s β t p j x i)
  simpa only [zero_smul,add_zero] using h

theorem hasDerivAt_vectorMagnetization_coordinate {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) (r : ℝ) :
    HasDerivAt (fun a => vectorMagnetization s β t p j (x+a • EuclideanSpace.single i (1 : ℝ)) i)
      ((vectorFieldHessian s β t p j (x+r • EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) i) r := by
  have hd := hasDerivAt_directional_on_affine_line (vectorRecursion s β t p j)
    ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)) x (EuclideanSpace.single i (1 : ℝ)) r
  have he : (fun a : ℝ => fderiv ℝ (vectorRecursion s β t p j)
      (x+a • EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)))=
      fun a : ℝ => vectorMagnetization s β t p j (x+a • EuclideanSpace.single i (1 : ℝ)) i :=
    funext fun a => fderiv_vectorRecursion_coordinate s β t p j _ i
  rw [he] at hd
  have hh : directionalHessian (vectorRecursion s β t p j)
      (x+r • EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))=
      (vectorFieldHessian s β t p j (x+r • EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) i := by
    simpa [vectorFieldHessian,directionalHessian,inner_hessianOperator,EuclideanSpace.inner_single_right] using
      (inner_hessianOperator (vectorRecursion s β t p j)
        (x+r • EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))).symm
  exact hd.congr_deriv hh

theorem norm_toLp_le_l1 {n : ℕ} (y : Fin n → ℝ) : ‖WithLp.toLp 2 y‖ ≤ l1 y := by
  classical
  have he : WithLp.toLp 2 y=∑i : Fin n,y i • EuclideanSpace.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  rw [he]
  simpa only [norm_smul,Real.norm_eq_abs,EuclideanSpace.norm_single,norm_one,mul_one,l1] using
    norm_sum_le (Finset.univ) (fun i : Fin n => y i • EuclideanSpace.single i (1 : ℝ))

theorem pairedTiltMean_eq_vectorStepResponse {n : ℕ} (f g : Field n → ℝ)
    (hf : Continuous f) (hg : Continuous g) (v m : ℝ) (x : Field n) :
    pairedTiltMean m v (fun y => f (WithLp.toLp 2 y)) (fun y => g (WithLp.toLp 2 y)) x.ofLp=
      vectorStepResponse v m f g x := by
  have hs : Continuous (fieldShift v x) := by unfold fieldShift;fun_prop
  have hi : Continuous (fun z => vectorStepWeight v m f x z*g (fieldShift v x z)) := by
    unfold vectorStepWeight
    exact ((Real.continuous_exp.comp (continuous_const.mul (hf.comp hs))).div_const _).mul (hg.comp hs)
  unfold vectorStepResponse
  rw [integral_fieldGaussian _ hi]
  unfold pairedTiltMean
  apply integral_congr_ae
  exact .of_forall fun z => by
    dsimp only
    rw [tiltWeightPi_eq_exp_div]
    have he : fieldShift v x (WithLp.toLp 2 z)=
        WithLp.toLp 2 (fun i => x i+Real.sqrt v*z i) := by ext i;rfl
    rw [he]
    unfold vectorStepWeight vectorStepPartition
    have hP : (∫w,Real.exp (m*f (fieldShift v x w)) ∂fieldGaussian n)=
        ∫w : Fin n → ℝ,Real.exp (m*f (fieldShift v x (WithLp.toLp 2 w))) ∂piGauss n :=
      integral_fieldGaussian (fun w => Real.exp (m*f (fieldShift v x w)))
        (Real.continuous_exp.comp (continuous_const.mul (hf.comp hs)))
    rw [hP,he]
    have hw (w : Fin n → ℝ) : fieldShift v x (WithLp.toLp 2 w)=
        WithLp.toLp 2 (fun i => x i+Real.sqrt v*w i) := by ext i;rfl
    simp_rw [hw]
    ring

theorem hasDerivAt_vectorColeHopfStep_variance_pi {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (m : ℝ) (x : Field n)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun u => vectorColeHopfStep u m (vectorRecursion s β t p j) x)
      ((∑i : Fin n,pairedTiltMean m v (fun y => vectorRecursion s β t p j (WithLp.toLp 2 y))
        (fun y => (vectorFieldHessian s β t p j (WithLp.toLp 2 y) (EuclideanSpace.single i (1 : ℝ))) i+
          m*(vectorMagnetization s β t p j (WithLp.toLp 2 y) i)^2) x.ofLp)/2) v := by
  classical
  let f := vectorRecursion s β t p j
  let A := fun y : Fin n → ℝ => f (WithLp.toLp 2 y)
  let A₁ := fun i : Fin n => fun y : Fin n → ℝ => vectorMagnetization s β t p j (WithLp.toLp 2 y) i
  let A₂ := fun i : Fin n => fun y : Fin n → ℝ =>
    (vectorFieldHessian s β t p j (WithLp.toLp 2 y) (EuclideanSpace.single i (1 : ℝ))) i
  let K := Real.sqrt (n : ℝ)
  obtain ⟨H,hH,hBound⟩ := exists_vectorFieldHessian_component_bound (n := n) s β t j
  have hA : Measurable A := ((vectorRecursion_lipschitz s β t p j).continuous.measurable).comp
    (WithLp.measurable_toLp 2 _)
  have h₁ (i : Fin n) : Measurable (A₁ i) :=
    ((boundedJets_vectorMagnetization_component s β t j i).1.continuous.measurable).comp
      (measurable_const.prodMk (WithLp.measurable_toLp 2 _))
  have h₂ (i : Fin n) : Measurable (A₂ i) :=
    (continuous_vectorFieldHessian_component s β t j i i).measurable.comp
      (measurable_const.prodMk (WithLp.measurable_toLp 2 _))
  have hg (y : Fin n → ℝ) : |A y| ≤ |f 0|+K*l1 y := by
    have h := abs_fieldShift_lipschitz f (Real.sqrt (n : ℝ)).toNNReal
      (vectorRecursion_lipschitz s β t p j) 1 0 (WithLp.toLp 2 y)
    simp only [fieldShift,zero_add,Real.sqrt_one,one_smul,one_mul,mul_one,
      Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at h
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_toLp_le_l1 y) (Real.sqrt_nonneg (n : ℝ))))
  have hline (y z : Fin n → ℝ) (r : ℝ) :
      HasDerivAt (fun a => A (y+a • z)) (∑i,z i*A₁ i (y+r • z)) r := by
    have h := hasDerivAt_vectorRecursion_field_gradient s β t p j
      (WithLp.toLp 2 y) (WithLp.toLp 2 z) r
    simpa [A,A₁,PiLp.inner_apply,RCLike.inner_apply,mul_comm] using h
  have hsecond (i : Fin n) (y : Fin n → ℝ) (r : ℝ) :
      HasDerivAt (fun a => A₁ i (y+a • Pi.single i 1)) (A₂ i (y+r • Pi.single i 1)) r := by
    simpa [A₁,A₂] using hasDerivAt_vectorMagnetization_coordinate s β t p j (WithLp.toLp 2 y) i r
  have hd := hasDerivAt_parisiStepPi_variance (Real.sqrt_nonneg (n : ℝ)) zero_le_one hA h₁ h₂ hg
    (fun i y => vectorMagnetization_component_bound s β t p j _ i)
    (fun i y => hBound (p,WithLp.toLp 2 y) i i) hline hsecond m x.ofLp hv
  have he : (fun u => vectorColeHopfStep u m f x)=fun u => parisiStepPi n m u A x.ofLp :=
    funext fun u => vectorColeHopfStep_eq_pi f (vectorRecursion_lipschitz s β t p j).continuous u m x
  rw [he]
  exact hd

theorem hasDerivAt_vectorColeHopfStep_variance {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (m : ℝ) (x : Field n)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun u => vectorColeHopfStep u m (vectorRecursion s β t p j) x)
      ((∑i : Fin n,vectorStepResponse v m (vectorRecursion s β t p j)
        (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i+
          m*(vectorMagnetization s β t p j y i)^2) x)/2) v := by
  have hd := hasDerivAt_vectorColeHopfStep_variance_pi s β t p j m x hv
  convert hd using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (pairedTiltMean_eq_vectorStepResponse _ _
    (vectorRecursion_lipschitz s β t p j).continuous
    (((continuous_vectorFieldHessian_component s β t j i i).comp
      (continuous_const.prodMk continuous_id)).add
      (continuous_const.mul (((boundedJets_vectorMagnetization_component s β t j i).1.continuous.comp
        (continuous_const.prodMk continuous_id)).pow 2))) v m x).symm

end QuantitativePaper
