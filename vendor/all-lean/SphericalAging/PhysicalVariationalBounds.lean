module

public import SphericalAging.LandscapeSphereGeometry
public import SphericalAging.HamiltonianVariational
public import SphericalAging.HamiltonianCoefficientBounds
public import SphericalAging.HamiltonianParameter

public section

/-! Actual finite-N physical variational coefficient bounds. The noise
square trace is calculated from the differentiated tangent projection;
its dimension factor is proved rather than assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.PhysicalVariationalBounds
open HardSphereDynamics FiniteModel GaussianLandscape LandscapeDerivatives
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem fderiv_noiseColumn_apply {N : ℕ} (x v : State N) (i : Fin N) :
    fderiv ℝ (fun y : State N => noiseColumn y i) x v=
      Real.sqrt 2 • projectionDerivative x v (basisVector i) := by
  have hd := ((differentiable_projection (basisVector i) x).hasFDerivAt.const_smul (Real.sqrt 2)).fderiv
  change fderiv ℝ (fun y : State N => Real.sqrt 2 • projection y (basisVector i)) x = _ at hd
  unfold noiseColumn
  rw [hd]
  simp only [ContinuousLinearMap.smul_apply,fderiv_projection_apply]

theorem projectionDerivative_basis_norm_sq {N : ℕ} (hN : 0 < N)
    (x v : State N) (i : Fin N) :
    ‖projectionDerivative x v (basisVector i)‖^2=
      ((v i)^2*‖x‖^2+(x i)^2*‖v‖^2+2*(v i)*(x i)*inner ℝ x v)/(N : ℝ)^2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [← real_inner_self_eq_norm_sq]
  simp only [projectionDerivative,basis_inner,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,neg_sq]
  rw [real_inner_comm v x]
  field_simp
  ring

theorem coordinate_inner_sum {N : ℕ} (x v : State N) :
    ∑ i : Fin N,(v i)*(x i)=inner ℝ x v := by
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]

/-- Exact actual differentiated-noise matrix trace on the physical sphere. -/
theorem noise_derivative_square_trace {N : ℕ} (hN : 0 < N) (x v : State N)
    (hx : OnSphere x) :
    (∑ i : Fin N,‖fderiv ℝ (fun y : State N => noiseColumn y i) x v‖^2)=
      4/(N : ℝ)*‖v‖^2+4/(N : ℝ)^2*(inner ℝ x v)^2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hr : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hxx : ‖x‖^2=(N : ℝ) := (onSphere_iff_norm_sq x).mp hx
  simp_rw [fderiv_noiseColumn_apply,norm_smul,mul_pow,Real.norm_of_nonneg (Real.sqrt_nonneg _),hr,
    projectionDerivative_basis_norm_sq hN x v,hxx]
  have hcol (i : Fin N) : 2*((v i)^2*(N : ℝ)+(x i)^2*‖v‖^2+
      2*(v i)*(x i)*inner ℝ x v)/(N : ℝ)^2 =
      (2*(N : ℝ)/(N : ℝ)^2)*(v i)^2+
        (2*‖v‖^2/(N : ℝ)^2)*(x i)^2+
        (4*inner ℝ x v/(N : ℝ)^2)*((v i)*(x i)) := by ring
  have hcol' (i : Fin N) : 2*(((v i)^2*(N : ℝ)+(x i)^2*‖v‖^2+
      2*(v i)*(x i)*inner ℝ x v)/(N : ℝ)^2) =
      (2*(N : ℝ)/(N : ℝ)^2)*(v i)^2+
        (2*‖v‖^2/(N : ℝ)^2)*(x i)^2+
        (4*inner ℝ x v/(N : ℝ)^2)*((v i)*(x i)) := by
    simpa only [mul_div_assoc] using hcol i
  simp_rw [hcol']
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    ← Finset.mul_sum,coordinate_square_sum v,coordinate_square_sum x,hx,
    real_inner_self_eq_norm_sq,coordinate_inner_sum]
  field_simp
  ring

/-- The actual noise Jacobian square trace is bounded with its true 1/N factor. -/
theorem noise_derivative_square_trace_le {N : ℕ} (hN : 0 < N) (x v : State N)
    (hx : OnSphere x) :
    (∑ i : Fin N,‖fderiv ℝ (fun y : State N => noiseColumn y i) x v‖^2) ≤
      8/(N : ℝ)*‖v‖^2 := by
  rw [noise_derivative_square_trace hN x v hx]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℝ) x v) 2
  simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hc
  have hxx := (onSphere_iff_norm_sq x).mp hx
  rw [hxx] at hc
  field_simp
  nlinarith

theorem projectionDerivative_norm_le {N : ℕ} (hN : 0 < N)
    (x v g : State N) (hx : OnSphere x) :
    ‖projectionDerivative x v g‖ ≤ 2*‖g‖/Real.sqrt (N : ℝ)*‖v‖ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hxx := (onSphere_iff_norm_sq x).mp hx
  have hnorm := sphere_norm x hxx
  have hs := Real.sq_sqrt hn.le
  calc
    ‖projectionDerivative x v g‖ ≤ ‖(inner ℝ v g/(N : ℝ)) • x‖+
        ‖(inner ℝ x g/(N : ℝ)) • v‖ := by
      simpa only [projectionDerivative,neg_smul,norm_neg] using
        norm_sub_le (-((inner ℝ v g/(N : ℝ)) • x)) ((inner ℝ x g/(N : ℝ)) • v)
    _ = ‖inner ℝ v g‖/(N : ℝ)*‖x‖+‖inner ℝ x g‖/(N : ℝ)*‖v‖ := by
      simp only [norm_smul,norm_div,Real.norm_of_nonneg hn.le,norm_neg]
    _ ≤ (‖v‖*‖g‖)/(N : ℝ)*‖x‖+(‖x‖*‖g‖)/(N : ℝ)*‖v‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (norm_inner_le_norm v g) hn.le) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (norm_inner_le_norm x g) hn.le) (norm_nonneg _))
    _ = _ := by rw [hnorm];field_simp;rw [hs];ring

theorem fderiv_hamiltonianDrift_apply {N p : ℕ} (β : ℝ) (J : Disorder N p)
    (x v : State N) :
    fderiv ℝ (hamiltonianDrift β J) x v = β •
      (projection x (fderiv ℝ (hamiltonianGradient J) x v)+
        projectionDerivative x v (hamiltonianGradient J x))-kappa N • v := by
  have hg := (hamiltonianGradient_contDiff J).differentiable (by simp) x
  have hi : DifferentiableAt ℝ (fun y : State N => inner ℝ y (hamiltonianGradient J y)) x := by
    simpa only [id_eq] using differentiableAt_id.inner ℝ hg
  have hc : DifferentiableAt ℝ (fun y : State N => inner ℝ y (hamiltonianGradient J y)/(N : ℝ)) x :=
    by simpa only [div_eq_mul_inv] using hi.mul_const (N : ℝ)⁻¹
  have hpg : DifferentiableAt ℝ (LandscapeSphereGeometry.projectedGradient (hamiltonianGradient J)) x := by
    unfold LandscapeSphereGeometry.projectedGradient
    simp only [tangentProjection_apply,projection]
    exact hg.sub (hc.smul differentiableAt_id)
  have hd := ((hpg.hasFDerivAt.const_smul β).sub
    (hasFDerivAt_id x |>.const_smul (kappa N))).fderiv
  change fderiv ℝ (fun y : State N => β • LandscapeSphereGeometry.projectedGradient (hamiltonianGradient J) y - kappa N • y) x = _ at hd
  have hfun : hamiltonianDrift β J = fun y : State N => β •
      LandscapeSphereGeometry.projectedGradient (hamiltonianGradient J) y - kappa N • y := by
    funext y
    simp only [hamiltonianDrift,drift,LandscapeSphereGeometry.projectedGradient,tangentProjection_apply]
  rw [hfun,hd]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [LandscapeSphereGeometry.projectedGradient_fderiv_apply _ x v hg]
  simp only [projection,projectionDerivative]
  rw [add_div]
  module

theorem kappa_norm_le_one {N : ℕ} (hN : 0 < N) : ‖kappa N‖ ≤ 1 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : 0 ≤ kappa N := div_nonneg (sub_nonneg.mpr h1) hn.le
  rw [Real.norm_of_nonneg hk]
  exact (div_le_iff₀ hn).mpr (by linarith)

/-- Dimension-independent physical drift Jacobian bound from the actual
Gaussian multilinear landscape seminorm. -/
theorem hamiltonianDrift_derivative_norm_le {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    {β : ℝ} (hβ : 0 ≤ β) (J : Disorder N p) (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (hamiltonianDrift β J) x v‖ ≤
      (1+β*(p : ℝ)*((p : ℝ)+1)*landscapeNorm N p J)*‖v‖ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr := Real.sqrt_pos.mpr hn
  have hxx := (onSphere_iff_norm_sq x).mp hx
  have hH : ‖fderiv ℝ (hamiltonianGradient J) x‖ ≤
      (p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J :=
    Hamiltonian_hessian_sphere_bound hN hp J x hxx
  have hg : ‖hamiltonianGradient J x‖/Real.sqrt (N : ℝ) ≤
      (p : ℝ)*landscapeNorm N p J := Hamiltonian_gradient_sphere_bound hN J x hxx
  have hP : ‖projection x (fderiv ℝ (hamiltonianGradient J) x v)‖ ≤
      (p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J*‖v‖ :=
    (projection_norm_le_onSphere (Nat.ne_of_gt hN) x _ hx).trans
      (((fderiv ℝ (hamiltonianGradient J) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hH (norm_nonneg _)))
  have hd : ‖projectionDerivative x v (hamiltonianGradient J x)‖ ≤
      2*((p : ℝ)*landscapeNorm N p J)*‖v‖ := by
    refine (projectionDerivative_norm_le hN x v _ hx).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num)) (norm_nonneg _)
  rw [fderiv_hamiltonianDrift_apply]
  calc
    _ ≤ ‖β • (projection x (fderiv ℝ (hamiltonianGradient J) x v)+
      projectionDerivative x v (hamiltonianGradient J x))‖+‖kappa N • v‖ := norm_sub_le _ _
    _ = β*‖projection x (fderiv ℝ (hamiltonianGradient J) x v)+
      projectionDerivative x v (hamiltonianGradient J x)‖+‖kappa N‖*‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg hβ]
    _ ≤ β*((p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J*‖v‖+
        2*((p : ℝ)*landscapeNorm N p J)*‖v‖)+1*‖v‖ :=
      add_le_add (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hP hd)) hβ)
        (mul_le_mul_of_nonneg_right (kappa_norm_le_one hN) (norm_nonneg _))
    _ = _ := by ring

/-- Smooth cutoff and physical coefficients have exactly the same actual
Fréchet derivative at every point strictly inside the cutoff radius. -/
theorem fderiv_cutoffCoefficient_eq {N : ℕ} (R : ℝ) (hR : 0 < R)
    (g : State N → State N) (x : State N) (hx : ‖x‖ < R) :
    fderiv ℝ (cutoffCoefficient R hR g) x = fderiv ℝ g x := by
  have hn : ∀ᶠ y in 𝓝 x, ‖y‖ < R :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx
  have he : cutoffCoefficient R hR g =ᶠ[𝓝 x] g := by
    filter_upwards [hn] with y hy
    exact cutoffCoefficient_eq R hR g y hy.le
  exact he.fderiv_eq

theorem fderiv_cutoffDrift_apply {N p : ℕ} (β : ℝ) (J : Disorder N p)
    (R : ℝ) (hR : 0 < R) (x v : State N) (hx : ‖x‖ < R) (i : Fin N) :
    fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i) x v =
      (fderiv ℝ (hamiltonianDrift β J) x v) i := by
  have he : CutoffSDE.cutoffDrift β J R hR i =ᶠ[𝓝 x]
      (fun y : State N => (hamiltonianDrift β J y) i) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact CutoffSDE.cutoffDrift_eq β J R hR y hy.le i
  rw [he.fderiv_eq]
  exact congrArg (fun f : State N →L[ℝ] ℝ => f v)
    ((VariationalCoefficients.coordinate i).hasFDerivAt.comp x
      ((contDiff_hamiltonianDrift β J).differentiable (by simp) x).hasFDerivAt).fderiv

theorem fderiv_cutoffNoise_apply {N : ℕ} (R : ℝ) (hR : 0 < R)
    (x v : State N) (hx : ‖x‖ < R) (i j : Fin N) :
    fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) x v =
      (fderiv ℝ (fun y : State N => noiseColumn y j) x v) i := by
  have he : CutoffSDE.cutoffNoise N R hR i j =ᶠ[𝓝 x]
      (fun y : State N => (noiseColumn y j) i) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact CutoffSDE.cutoffNoise_eq N R hR y hy.le i j
  rw [he.fderiv_eq]
  exact congrArg (fun f : State N →L[ℝ] ℝ => f v)
    ((VariationalCoefficients.coordinate i).hasFDerivAt.comp x
      ((contDiff_noiseColumn j).differentiable (by simp) x).hasFDerivAt).fderiv

theorem cutoff_noise_square_trace_le {N : ℕ} (hN : 0 < N)
    (R : ℝ) (hR : 0 < R) (x v : State N) (hx : OnSphere x) (hxR : ‖x‖ < R) :
    (∑ j : Fin N,∑ i : Fin N,(fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) x v)^2) ≤
      8/(N : ℝ)*‖v‖^2 := by
  simp_rw [fderiv_cutoffNoise_apply R hR x v hxR]
  simp_rw [coordinate_square_sum,real_inner_self_eq_norm_sq]
  exact noise_derivative_square_trace_le hN x v hx

/-- A single actual ordered Gaussian coupling has dimension-independent
physical drift forcing norm βp, with the manuscript's normalization. -/
theorem couplingDrift_sphere_norm_le {N p : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β)
    (R : ℝ) (hR : 0 < R) (I : TensorIndex N p) (x : State N)
    (hx : OnSphere x) (hxR : ‖x‖ ≤ R) :
    ‖HamiltonianParameter.couplingDrift β R hR I x‖ ≤ β*(p : ℝ) := by
  have hb : coefficientBump (N := N) R hR x=1 := by
    apply (coefficientBump (N := N) R hR).one_of_mem_closedBall
    simpa only [coefficientBump,Metric.mem_closedBall,dist_zero_right] using hxR
  simp only [HamiltonianParameter.couplingDrift,hb,one_smul,norm_smul,Real.norm_of_nonneg hβ]
  apply mul_le_mul_of_nonneg_left _ hβ
  refine (projection_norm_le_onSphere (Nat.ne_of_gt hN) x _ hx).trans ?_
  simpa only [HamiltonianCoefficientBounds.coefficient_eq_basisHamiltonian,
    HamiltonianCoefficientBounds.basisDisorder,HamiltonianParameter.disorderBasis,hamiltonianGradient] using
    HamiltonianCoefficientBounds.coefficient_gradient_sphere_bound hN I x
      ((onSphere_iff_norm_sq x).mp hx)

end SphericalAging.PhysicalVariationalBounds
