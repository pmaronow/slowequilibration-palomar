module
public import QuantitativePaper.VectorHeatCalculus

@[expose] public section

/-! Spatial derivatives of the genuine Gaussian step applied to the actual
vector recursion. The first and second derivatives are its normalized tilted
responses, including zero variance and zero mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem vectorStepResponse_translate {n : ℕ} (f g : Field n → ℝ) (c m : ℝ)
    (x w : Field n) :
    vectorStepResponse c m (fun z => f (z+w)) (fun z => g (z+w)) x=
      vectorStepResponse c m f g (x+w) := by
  have he (z : Field n) : fieldShift c x z+w=fieldShift c (x+w) z := by
    unfold fieldShift
    abel
  unfold vectorStepResponse vectorStepWeight vectorStepPartition
  simp_rw [he]

theorem vectorStepSecondResponse_translate {n : ℕ} (f g h : Field n → ℝ) (c m : ℝ)
    (x w : Field n) :
    vectorStepSecondResponse c m (fun z => f (z+w)) (fun z => g (z+w))
      (fun z => h (z+w)) x=vectorStepSecondResponse c m f g h (x+w) := by
  unfold vectorStepSecondResponse
  rw [vectorStepResponse_translate f h c m x w,
    vectorStepResponse_translate f (fun y => g y^2) c m x w,
    vectorStepResponse_translate f g c m x w]

theorem contDiff_vectorColeHopfStep_recursion_joint {n k : ℕ} (s : RSBScheme k)
    (β t c m : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : VectorParameter n =>
      vectorColeHopfStep c m (vectorRecursion s β t p.1 j) p.2) := by
  apply contDiff_infty.mpr
  intro N
  obtain ⟨hSmooth,K,hK,hJets⟩ := vectorRecursion_joint_smooth_bounded_jets (n := n) s β t N j
  have hh := gaussianShiftColeHopf_smooth_bounded_jets N
    (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) hSmooth
    (vectorJointLipschitzConstant n β t) (vectorRecursion_joint_lipschitz s β t j)
    K hK hJets (vectorJointShift n c) m
  have he : gaussianShiftColeHopf (vectorJointShift n c) m
      (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2)=
      fun p : VectorParameter n => vectorColeHopfStep c m (vectorRecursion s β t p.1 j) p.2 := by
    funext p
    exact gaussianShiftColeHopf_vectorRecursion s β t c m j p
  rw [he] at hh
  exact hh.1

theorem contDiff_vectorColeHopfStep_recursion_field {n k : ℕ} (s : RSBScheme k)
    (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (vectorColeHopfStep c m (vectorRecursion s β t p j)) :=
  (contDiff_vectorColeHopfStep_recursion_joint s β t c m j).comp
    (contDiff_const.prodMk contDiff_id)

theorem hasDerivAt_vectorColeHopfStep_recursion_coordinate {n k : ℕ}
    (s : RSBScheme k) (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ)
    (x : Field n) (i : Fin n) (r : ℝ) :
    HasDerivAt (fun a : ℝ => vectorColeHopfStep c m (vectorRecursion s β t p j)
      (x+a • EuclideanSpace.single i (1 : ℝ)))
      (vectorStepResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i)
        (x+r • EuclideanSpace.single i (1 : ℝ))) r := by
  let e : Field n := EuclideanSpace.single i 1
  let f := fun a : ℝ => fun y : Field n => vectorRecursion s β t p j (y+a • e)
  let v := fun a : ℝ => fun y : Field n => vectorMagnetization s β t p j (y+a • e) i
  have hf (a : ℝ) : LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (f a) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa [f,dist_eq_norm] using (vectorRecursion_lipschitz s β t p j).dist_le_mul (y+a • e) (z+a • e)
  have hv (a : ℝ) : Measurable (v a) := by
    exact (((boundedJets_vectorMagnetization_component s β t j i).1.continuous.comp
      (continuous_const.prodMk (continuous_id.add continuous_const))).measurable)
  have hd (a : ℝ) (y : Field n) : HasDerivAt (fun b => f b y) (v a y) a := by
    simpa [f,v,e,EuclideanSpace.inner_single_right] using
      hasDerivAt_vectorRecursion_field_gradient s β t p j y e a
  have hh := hasDerivAt_vectorColeHopfStep_response f v (Real.sqrt (n : ℝ)).toNNReal 1
    hf hv (fun a y => vectorMagnetization_component_bound s β t p j (y+a • e) i)
    hd c m x r
  have he : vectorStepResponse c m (f r) (v r) x=
      vectorStepResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i) (x+r • e) :=
    vectorStepResponse_translate (vectorRecursion s β t p j)
      (fun y => vectorMagnetization s β t p j y i) c m x (r • e)
  rw [he] at hh
  simpa only [f,vectorColeHopfStep_translate,e] using hh

theorem fderiv_vectorColeHopfStep_recursion_coordinate {n k : ℕ}
    (s : RSBScheme k) (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ)
    (x : Field n) (i : Fin n) :
    fderiv ℝ (vectorColeHopfStep c m (vectorRecursion s β t p j)) x
      (EuclideanSpace.single i (1 : ℝ))=
      vectorStepResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i) x := by
  have hh := (hasDerivAt_on_affine_line _
    ((contDiff_vectorColeHopfStep_recursion_field s β t c m p j).of_le (by simp))
    x (EuclideanSpace.single i (1 : ℝ)) 0).unique
    (hasDerivAt_vectorColeHopfStep_recursion_coordinate s β t c m p j x i 0)
  simpa only [zero_smul,add_zero] using hh

theorem hasDerivAt_vectorStepResponse_recursion_coordinate {n k : ℕ}
    (s : RSBScheme k) (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ)
    (x : Field n) (i : Fin n) (r : ℝ) :
    HasDerivAt (fun a : ℝ => vectorStepResponse c m (vectorRecursion s β t p j)
      (fun y => vectorMagnetization s β t p j y i)
      (x+a • EuclideanSpace.single i (1 : ℝ)))
      (vectorStepSecondResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i)
        (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i)
        (x+r • EuclideanSpace.single i (1 : ℝ))) r := by
  let e : Field n := EuclideanSpace.single i 1
  let f := fun a : ℝ => fun y : Field n => vectorRecursion s β t p j (y+a • e)
  let v := fun a : ℝ => fun y : Field n => vectorMagnetization s β t p j (y+a • e) i
  let w := fun a : ℝ => fun y : Field n => (vectorFieldHessian s β t p j (y+a • e) e) i
  have hf (a : ℝ) : LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (f a) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa [f,dist_eq_norm] using (vectorRecursion_lipschitz s β t p j).dist_le_mul (y+a • e) (z+a • e)
  have hv (a : ℝ) : Measurable (v a) :=
    ((boundedJets_vectorMagnetization_component s β t j i).1.continuous.comp
      (continuous_const.prodMk (continuous_id.add continuous_const))).measurable
  have hw (a : ℝ) : Measurable (w a) :=
    ((continuous_vectorFieldHessian_component s β t j i i).comp
      (continuous_const.prodMk (continuous_id.add continuous_const))).measurable
  obtain ⟨H,hH,hBound⟩ := exists_vectorFieldHessian_component_bound (n := n) s β t j
  have hb (a : ℝ) (y : Field n) : |w a y| ≤ H.toNNReal := by
    rw [Real.coe_toNNReal _ hH]
    exact hBound (p,y+a • e) i i
  have hdf (a : ℝ) (y : Field n) : HasDerivAt (fun b => f b y) (v a y) a := by
    simpa [f,v,e,EuclideanSpace.inner_single_right] using
      hasDerivAt_vectorRecursion_field_gradient s β t p j y e a
  have hdv (a : ℝ) (y : Field n) : HasDerivAt (fun b => v b y) (w a y) a :=
    hasDerivAt_vectorMagnetization_coordinate s β t p j y i a
  have hh := hasDerivAt_vectorStepResponse f v w (Real.sqrt (n : ℝ)).toNNReal 1 H.toNNReal
    hf hv hw (fun a y => vectorMagnetization_component_bound s β t p j (y+a • e) i)
    hb hdf hdv c m x r
  have he : vectorStepSecondResponse c m (f r) (v r) (w r) x=
      vectorStepSecondResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i)
        (fun y => (vectorFieldHessian s β t p j y e) i) (x+r • e) := by
    exact vectorStepSecondResponse_translate (vectorRecursion s β t p j)
      (fun y => vectorMagnetization s β t p j y i)
      (fun y => (vectorFieldHessian s β t p j y e) i) c m x (r • e)
  rw [he] at hh
  have hfun : (fun a => vectorStepResponse c m (f a) (v a) x)=
      fun a => vectorStepResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i) (x+a • e) := by
    funext a
    exact vectorStepResponse_translate (vectorRecursion s β t p j)
      (fun y => vectorMagnetization s β t p j y i) c m x (a • e)
  rw [hfun] at hh
  exact hh

theorem directionalHessian_vectorColeHopfStep_recursion_coordinate {n k : ℕ}
    (s : RSBScheme k) (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ)
    (x : Field n) (i : Fin n) :
    directionalHessian (vectorColeHopfStep c m (vectorRecursion s β t p j)) x
      (EuclideanSpace.single i (1 : ℝ))=
      vectorStepSecondResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i)
        (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i) x := by
  let F := vectorColeHopfStep c m (vectorRecursion s β t p j)
  have hh := hasDerivAt_directional_on_affine_line F
    ((contDiff_vectorColeHopfStep_recursion_field s β t c m p j).of_le (by simp))
    x (EuclideanSpace.single i (1 : ℝ)) 0
  have he : (fun a : ℝ => fderiv ℝ F (x+a • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)))=
      fun a : ℝ => vectorStepResponse c m (vectorRecursion s β t p j)
        (fun y => vectorMagnetization s β t p j y i) (x+a • EuclideanSpace.single i (1 : ℝ)) :=
    funext fun a => fderiv_vectorColeHopfStep_recursion_coordinate s β t c m p j _ i
  rw [he] at hh
  simpa only [zero_smul,add_zero] using
    hh.unique (hasDerivAt_vectorStepResponse_recursion_coordinate s β t c m p j x i 0)

end QuantitativePaper
