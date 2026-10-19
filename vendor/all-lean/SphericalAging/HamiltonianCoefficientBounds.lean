module

public import SphericalAging.HamiltonianDerivativeCovariance
public import SphericalAging.HardSphereStochastic

public section

/-! Genuine uniform sphere bounds for individual ordered Hamiltonian
coefficients and their gradients, and automatic Gaussian integrability of
bounded sphere observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.HamiltonianCoefficientBounds
open FiniteModel GaussianIntegrationByParts GaussianLandscape LandscapeDerivatives
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem coordinateForm_norm_le {N p : ℕ} (I : TensorIndex N p) :
    ‖coordinateForm N p I‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro v
  simp only [coordinateForm,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply,PiLp.proj_apply,one_mul]
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k _ => PiLp.norm_apply_le (v k) (I k))

@[expose] def basisDisorder {N p : ℕ} (I : TensorIndex N p) : Disorder N p := Pi.single I 1

theorem tensorForm_basisDisorder {N p : ℕ} (I : TensorIndex N p) :
    tensorForm N p (basisDisorder I)=coordinateForm N p I := by
  classical
  simp [tensorForm,basisDisorder,Pi.single_apply]

theorem coefficient_eq_basisHamiltonian {N p : ℕ} (I : TensorIndex N p) :
    hamiltonianCoefficient I=Hamiltonian N p (basisDisorder I) := by
  classical
  funext x
  rw [hamiltonian_eq_sum_coefficients]
  simp [basisDisorder,Pi.single_apply]

/-- Each actual coefficient gradient is bounded by `p`, independently of N. -/
theorem coefficient_gradient_sphere_bound {N p : ℕ} (hN : 0 < N)
    (I : TensorIndex N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    ‖gradient (hamiltonianCoefficient I) x‖ ≤ p := by
  rw [coefficient_eq_basisHamiltonian]
  have hh := Hamiltonian_gradient_norm_le (basisDisorder I) x
  rw [tensorForm_basisDisorder,sphere_norm x hx] at hh
  have he : normalization N p*(p : ℝ)*‖coordinateForm N p I‖*Real.sqrt (N : ℝ)^(p-1)=
      (p : ℝ)*‖coordinateForm N p I‖ := by
    calc
      _ = (p : ℝ)*‖coordinateForm N p I‖*(normalization N p*Real.sqrt (N : ℝ)^(p-1)) := by ring
      _ = _ := by rw [normalization_sqrt_power hN];ring
  rw [he] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (coordinateForm_norm_le I) (Nat.cast_nonneg p)).trans_eq (mul_one _))

/-- Individual ordered coefficients are bounded by sqrt(N) on the actual sphere. -/
theorem coefficient_sphere_bound {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (I : TensorIndex N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    |hamiltonianCoefficient I x| ≤ Real.sqrt (N : ℝ) := by
  have hh := Hamiltonian_sphere_bound hN hp (basisDisorder I) x hx
  rw [← coefficient_eq_basisHamiltonian] at hh
  unfold landscapeNorm at hh
  rw [tensorForm_basisDisorder] at hh
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  apply (div_le_div_iff_of_pos_right hNr).mp
  calc
    _ ≤ ‖coordinateForm N p I‖/Real.sqrt (N : ℝ) := hh
    _ ≤ 1/Real.sqrt (N : ℝ) := div_le_div_of_nonneg_right (coordinateForm_norm_le I) hr.le
    _ = Real.sqrt (N : ℝ)/(N : ℝ) := by
      field_simp
      exact (Real.sq_sqrt hNr.le).symm

/-- Any measurable sphere-valued family gives automatic L² integrability
of every actual ordered Hamiltonian coefficient. -/
theorem coefficient_memLp_of_sphere {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (hN : 0 < N) (hp : 1 ≤ p)
    (I : TensorIndex N p) (X : Ω → Vector N) (hXm : AEStronglyMeasurable X ν)
    (hXs : ∀ᵐ ω ∂ν,‖X ω‖^2=(N : ℝ)) :
    MemLp (fun ω => hamiltonianCoefficient I (X ω)) 2 ν := by
  apply MemLp.of_bound ((HamiltonianDerivativeCovariance.coefficient_contDiff I).continuous.comp_aestronglyMeasurable hXm)
    (Real.sqrt (N : ℝ))
  filter_upwards [hXs] with ω hω
  exact coefficient_sphere_bound hN hp I (X ω) hω

/-- Gaussian coefficient times a bounded sphere observable is automatically
integrable under actual iid disorder and independent auxiliary randomness. -/
theorem gaussian_coordinate_coefficient_integrable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hN : 0 < N) (hp : 1 ≤ p)
    (I : TensorIndex N p) (X : Disorder N p × Ω → Vector N)
    (hXm : AEStronglyMeasurable X ((disorderLaw N p).prod ν))
    (hXs : ∀ᵐ q ∂(disorderLaw N p).prod ν,‖X q‖^2=(N : ℝ)) :
    Integrable (fun q => q.1 I*hamiltonianCoefficient I (X q)) ((disorderLaw N p).prod ν) := by
  have hJ : MemLp (fun q : Disorder N p × Ω => q.1 I) 2 ((disorderLaw N p).prod ν) :=
    (coordinate_memLp N p I).comp_fst ν
  have hF := coefficient_memLp_of_sphere hN hp I X hXm hXs
  exact memLp_one_iff_integrable.mp (hJ.mul hF)

/-- The same uniform gradient bound holds on the entire convex sphere ball. -/
theorem coefficient_gradient_ball_bound {N p : ℕ} (hN : 0 < N)
    (I : TensorIndex N p) (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) :
    ‖gradient (hamiltonianCoefficient I) x‖ ≤ p := by
  rw [coefficient_eq_basisHamiltonian]
  have hh := Hamiltonian_gradient_norm_le (basisDisorder I) x
  rw [tensorForm_basisDisorder] at hh
  calc
    _ ≤ normalization N p*(p : ℝ)*‖coordinateForm N p I‖*‖x‖^(p-1) := hh
    _ ≤ normalization N p*(p : ℝ)*1*Real.sqrt (N : ℝ)^(p-1) := by
      have hn : 0 ≤ normalization N p := Real.rpow_nonneg (Nat.cast_nonneg N) _
      gcongr <;> first | positivity | exact coordinateForm_norm_le I
    _ = p := by
      calc
        _ = (p : ℝ)*(normalization N p*Real.sqrt (N : ℝ)^(p-1)) := by ring
        _ = _ := by rw [normalization_sqrt_power hN];ring

/-- Actual coefficient observables are p-Lipschitz on the sphere ball. -/
theorem coefficient_lipschitzOn_ball {N p : ℕ} (hN : 0 < N) (I : TensorIndex N p) :
    LipschitzOnWith (p : ℝ≥0) (hamiltonianCoefficient I)
      (Metric.closedBall 0 (Real.sqrt (N : ℝ))) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (HamiltonianDerivativeCovariance.coefficient_contDiff I).differentiable (by simp) x)
    ?_ (convex_closedBall 0 (Real.sqrt (N : ℝ)))
  intro x hx
  change ‖fderiv ℝ (hamiltonianCoefficient I) x‖ ≤ p
  have hb := coefficient_gradient_ball_bound hN I x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  simpa only [gradient,LinearIsometryEquiv.norm_map] using hb

/-- Pairing the actual coefficient gradient with a genuine L² variational
state is automatically integrable, by the proved uniform sphere bound. -/
theorem coefficient_gradient_pairing_integrable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (hN : 0 < N)
    (I : TensorIndex N p) (X V : Ω → Vector N) (hXm : AEStronglyMeasurable X ν)
    (hXs : ∀ᵐ ω ∂ν,‖X ω‖^2=(N : ℝ)) (hV : MemLp V 2 ν) :
    Integrable (fun ω => inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (V ω)) ν := by
  have hg : Continuous (gradient (hamiltonianCoefficient I)) := by
    rw [coefficient_eq_basisHamiltonian]
    exact (HardSphereDynamics.hamiltonianGradient_contDiff (basisDisorder I)).continuous
  have hm : MemLp (fun ω => inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (V ω)) 2 ν := by
    apply hV.norm.const_mul (p : ℝ) |>.of_le
      (((hg.comp_aestronglyMeasurable hXm).inner hV.aestronglyMeasurable))
    filter_upwards [hXs] with ω hω
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))]
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right (coefficient_gradient_sphere_bound hN I (X ω) hω) (norm_nonneg _))
  exact hm.integrable (by norm_num)

end SphericalAging.HamiltonianCoefficientBounds
