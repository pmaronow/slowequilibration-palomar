module

public import SphericalAging.SphereSurfaceIdentification
public import SphericalAging.LandscapeDerivatives
public import SphericalAging.GaussianLandscapeMoments
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.MGFAnalytic

public section

/-! Actual spherical Gibbs density and the initial quenched/annealed entropy
bounds. The sphere measure and Hamiltonian are the constructed model objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators InnerProductSpace NNReal
namespace SphericalAging.SphereGibbsEntropy
open FiniteModel SphereInitialLaw GaussianLandscape GaussianLandscapeMoments LandscapeDerivatives

@[expose] def partitionFunction (N p : ℕ) (β : ℝ) (J : Disorder N p) : ℝ :=
  ∫ x : Vector N,Real.exp (β*Hamiltonian N p J x) ∂sphereLaw N

@[expose] def gibbsDensity (N p : ℕ) (β : ℝ) (J : Disorder N p) (x : Vector N) : ℝ :=
  Real.exp (β*Hamiltonian N p J x)/partitionFunction N p β J

/-- The relative entropy of the actual uniform initial law with respect to Gibbs. -/
@[expose] def initialEntropy (N p : ℕ) (β : ℝ) (J : Disorder N p) : ℝ :=
  ∫ x : Vector N,-Real.log (gibbsDensity N p β J x) ∂sphereLaw N

theorem Hamiltonian_joint_continuous (N p : ℕ) :
    Continuous (fun z : Disorder N p × Vector N => Hamiltonian N p z.1 z.2) := by
  classical
  unfold Hamiltonian tensorMonomial
  fun_prop

theorem sphere_Hamiltonian_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p) (J : Disorder N p) :
    ∀ᵐ x ∂sphereLaw N,|Hamiltonian N p J x| ≤ (N : ℝ)*landscapeNorm N p J := by
  filter_upwards [sphereLaw_support hN] with x hx
  have hh := (div_le_iff₀ (Nat.cast_pos.mpr hN)).mp (Hamiltonian_sphere_bound hN hp J x hx)
  simpa only [mul_comm] using hh

theorem sphere_Hamiltonian_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) (J : Disorder N p) :
    Integrable (Hamiltonian N p J) (sphereLaw N) := by
  apply (integrable_const ((N : ℝ)*landscapeNorm N p J)).mono'
    (Hamiltonian_contDiff J).continuous.aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using sphere_Hamiltonian_bound hN hp J

theorem sphere_exp_Hamiltonian_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    (β : ℝ) (J : Disorder N p) :
    Integrable (fun x => Real.exp (β*Hamiltonian N p J x)) (sphereLaw N) := by
  apply (integrable_const (Real.exp (|β| *(N : ℝ)*landscapeNorm N p J))).mono'
    ((Real.continuous_exp.comp ((Hamiltonian_contDiff J).continuous.const_mul β)).aestronglyMeasurable)
  filter_upwards [sphere_Hamiltonian_bound hN hp J] with x hx
  simp only [Function.comp_def]
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  calc
    β*Hamiltonian N p J x ≤ |β*Hamiltonian N p J x| := le_abs_self _
    _ = |β| *|Hamiltonian N p J x| := abs_mul _ _
    _ ≤ |β| *((N : ℝ)*landscapeNorm N p J) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by ring

/-- Exact finite quenched partition bounds from the constructed tensor norm. -/
theorem partition_bounds {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    Real.exp (-β*(N : ℝ)*landscapeNorm N p J) ≤ partitionFunction N p β J ∧
      partitionFunction N p β J ≤ Real.exp (β*(N : ℝ)*landscapeNorm N p J) := by
  have hi := sphere_exp_Hamiltonian_integrable hN hp β J
  have hb := sphere_Hamiltonian_bound hN hp J
  constructor
  · have hh := integral_mono_ae (integrable_const (Real.exp (-β*(N : ℝ)*landscapeNorm N p J))) hi (by
      filter_upwards [hb] with x hx
      apply Real.exp_le_exp.mpr
      have hn := (abs_le.mp hx).1
      nlinarith only [mul_le_mul_of_nonneg_left hn hβ])
    simpa only [integral_const,probReal_univ,one_smul,partitionFunction] using hh
  · have hh := integral_mono_ae hi (integrable_const (Real.exp (β*(N : ℝ)*landscapeNorm N p J))) (by
      filter_upwards [hb] with x hx
      apply Real.exp_le_exp.mpr
      have hn := (abs_le.mp hx).2
      nlinarith only [mul_le_mul_of_nonneg_left hn hβ])
    simpa only [integral_const,probReal_univ,one_smul,partitionFunction] using hh

theorem partition_positive {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) : 0<partitionFunction N p β J :=
  (Real.exp_pos _).trans_le (partition_bounds hN hp hβ J).1

theorem log_partition_bounds {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    |Real.log (partitionFunction N p β J)| ≤ β*(N : ℝ)*landscapeNorm N p J := by
  have hp' := partition_positive hN hp hβ J
  have hb := partition_bounds hN hp hβ J
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_log (Real.exp_pos _) hb.1
    rw [Real.log_exp] at hh
    nlinarith only [hh]
  · have hh := Real.log_le_log hp' hb.2
    rw [Real.log_exp] at hh
    exact hh

/-- Genuine normalized Gibbs density, proved without a normalization premise. -/
theorem gibbsDensity_normalized {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    (∫ x : Vector N,gibbsDensity N p β J x ∂sphereLaw N)=1 := by
  simp only [gibbsDensity,integral_div]
  exact div_self (partition_positive hN hp hβ J).ne'

theorem gibbsDensity_positive {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) (x : Vector N) : 0<gibbsDensity N p β J x :=
  div_pos (Real.exp_pos _) (partition_positive hN hp hβ J)

theorem negative_log_gibbsDensity {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) (x : Vector N) :
    -Real.log (gibbsDensity N p β J x)=Real.log (partitionFunction N p β J)-β*Hamiltonian N p J x := by
  rw [gibbsDensity,Real.log_div (Real.exp_ne_zero _) (partition_positive hN hp hβ J).ne',Real.log_exp]
  ring

/-- The source's exact initial entropy formula is derived from the actual density. -/
theorem initialEntropy_formula {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    initialEntropy N p β J=Real.log (partitionFunction N p β J)-
      β*(∫ x : Vector N,Hamiltonian N p J x ∂sphereLaw N) := by
  unfold initialEntropy
  simp_rw [negative_log_gibbsDensity hN hp hβ J]
  rw [integral_sub (integrable_const _) ((sphere_Hamiltonian_integrable hN hp J).const_mul β),
    integral_const,probReal_univ,one_smul,integral_const_mul]

/-- Exact quenched initial entropy bound in Lemma 5.1. -/
theorem initialEntropy_abs_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    |initialEntropy N p β J| ≤ 2*β*(N : ℝ)*landscapeNorm N p J := by
  have hi := norm_integral_le_of_norm_le_const (μ := sphereLaw N) (f := Hamiltonian N p J)
    (C := (N : ℝ)*landscapeNorm N p J) (by simpa only [Real.norm_eq_abs] using sphere_Hamiltonian_bound hN hp J)
  simp only [Real.norm_eq_abs,probReal_univ,mul_one] at hi
  rw [initialEntropy_formula hN hp hβ J]
  calc
    _ ≤ |Real.log (partitionFunction N p β J)|+|β*(∫ x : Vector N,Hamiltonian N p J x ∂sphereLaw N)| := abs_sub _ _
    _ ≤ β*(N : ℝ)*landscapeNorm N p J+β*((N : ℝ)*landscapeNorm N p J) := by
      rw [abs_mul,abs_of_nonneg hβ]
      exact add_le_add (log_partition_bounds hN hp hβ J) (mul_le_mul_of_nonneg_left hi hβ)
    _ = _ := by ring


theorem gibbsDensity_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    (β : ℝ) (J : Disorder N p) : Integrable (gibbsDensity N p β J) (sphereLaw N) :=
  (sphere_exp_Hamiltonian_integrable hN hp β J).div_const _

theorem negative_log_gibbsDensity_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    Integrable (fun x => -Real.log (gibbsDensity N p β J x)) (sphereLaw N) := by
  have he : (fun x => -Real.log (gibbsDensity N p β J x))=
      (fun x => Real.log (partitionFunction N p β J)-β*Hamiltonian N p J x) := by
    funext x
    exact negative_log_gibbsDensity hN hp hβ J x
  rw [he]
  exact (integrable_const _).sub ((sphere_Hamiltonian_integrable hN hp J).const_mul β)

/-- Positivity of relative entropy is proved from the actual normalized density. -/
theorem initialEntropy_nonnegative {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) : 0 ≤ initialEntropy N p β J := by
  have hb (x : Vector N) : 1-gibbsDensity N p β J x ≤ -Real.log (gibbsDensity N p β J x) := by
    have hl := Real.log_le_sub_one_of_pos (gibbsDensity_positive hN hp hβ J x)
    linarith only [hl]
  have hh := integral_mono ((integrable_const (1 : ℝ)).sub (gibbsDensity_integrable hN hp β J))
    (negative_log_gibbsDensity_integrable hN hp hβ J) hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const _) (gibbsDensity_integrable hN hp β J),
    integral_const,probReal_univ,one_smul,gibbsDensity_normalized hN hp hβ J,sub_self] at hh
  exact hh

theorem partition_stronglyMeasurable (N p : ℕ) (β : ℝ) :
    StronglyMeasurable (partitionFunction N p β) :=
  (Real.continuous_exp.comp ((Hamiltonian_joint_continuous N p).const_mul β)).stronglyMeasurable.integral_prod_right'

theorem sphere_Hamiltonian_mean_stronglyMeasurable (N p : ℕ) :
    StronglyMeasurable (fun J : Disorder N p => ∫ x : Vector N,Hamiltonian N p J x ∂sphereLaw N) :=
  (Hamiltonian_joint_continuous N p).stronglyMeasurable.integral_prod_right'

theorem landscapeNorm_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) :
    Integrable (landscapeNorm N p) (disorderLaw N p) := by
  simpa only [Real.rpow_one] using (uniform_real_power_moment hN (show 0<p by omega)
    (k := 1) (by norm_num)).1

theorem joint_Hamiltonian_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) :
    Integrable (fun z : Disorder N p × Vector N => Hamiltonian N p z.1 z.2)
      ((disorderLaw N p).prod (sphereLaw N)) := by
  apply (((landscapeNorm_integrable hN hp).const_mul (N : ℝ)).comp_fst (sphereLaw N)).mono'
    (Hamiltonian_joint_continuous N p).aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (Hamiltonian_joint_continuous N p).norm.measurable
    (((landscapeNorm_continuous N p).comp continuous_fst).const_mul (N : ℝ)).measurable)).mpr
  exact Eventually.of_forall (fun J => by
    simpa only [Real.norm_eq_abs,Function.comp_def] using sphere_Hamiltonian_bound hN hp J)

theorem joint_exp_Hamiltonian_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) (β : ℝ) :
    Integrable (fun z : Disorder N p × Vector N => Real.exp (β*Hamiltonian N p z.1 z.2))
      ((disorderLaw N p).prod (sphereLaw N)) := by
  have hi := (uniform_exponential_moment hN (show 0<p by omega) (|β| *(N : ℝ))).1
  apply (hi.comp_fst (sphereLaw N)).mono'
    (Real.continuous_exp.comp ((Hamiltonian_joint_continuous N p).const_mul β)).aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (Real.continuous_exp.comp ((Hamiltonian_joint_continuous N p).const_mul β)).norm.measurable
    (Real.continuous_exp.comp (((landscapeNorm_continuous N p).comp continuous_fst).const_mul (|β| *(N : ℝ)))).measurable)).mpr
  apply Eventually.of_forall
  intro J
  filter_upwards [sphere_Hamiltonian_bound hN hp J] with x hx
  simp only [Function.comp_def]
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  calc
    β*Hamiltonian N p J x ≤ |β*Hamiltonian N p J x| := le_abs_self _
    _ = |β| *|Hamiltonian N p J x| := abs_mul _ _
    _ ≤ |β| *((N : ℝ)*landscapeNorm N p J) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by ring

theorem partition_annealed_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) (β : ℝ) :
    Integrable (partitionFunction N p β) (disorderLaw N p) :=
  (joint_exp_Hamiltonian_integrable hN hp β).integral_prod_left

/-- Actual Gaussian Hamiltonian law with exactly the manuscript's sphere variance N. -/
theorem Hamiltonian_sphere_hasLaw {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    HasLaw (fun J : Disorder N p => Hamiltonian N p J x) (gaussianReal 0 (N : ℝ≥0))
      (disorderLaw N p) := by
  have hG := Hamiltonian_hasGaussianLaw (p := p) x
  refine ⟨hG.aemeasurable,?_⟩
  rw [hG.map_eq_gaussianReal,Hamiltonian_mean,Hamiltonian_variance_on_sphere hN hp x hx]
  simp

/-- The genuine annealed sphere Hamiltonian MGF, no exponential moment premise. -/
theorem Hamiltonian_sphere_mgf {N p : ℕ} (hN : 0<N) (hp : 1≤p) (β : ℝ)
    (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    (∫ J : Disorder N p,Real.exp (β*Hamiltonian N p J x) ∂disorderLaw N p)=
      Real.exp (β^2*(N : ℝ)/2) := by
  have hh := mgf_gaussianReal (Hamiltonian_sphere_hasLaw hN hp x hx) β
  simpa only [mgf,zero_mul,zero_add,NNReal.coe_natCast,mul_comm (N : ℝ) (β^2)] using hh

/-- True partition expectation from Gaussian MGF and justified spherical Fubini. -/
theorem partition_annealed_mean {N p : ℕ} (hN : 0<N) (hp : 1≤p) (β : ℝ) :
    (∫ J : Disorder N p,partitionFunction N p β J ∂disorderLaw N p)=
      Real.exp (β^2*(N : ℝ)/2) := by
  unfold partitionFunction
  rw [integral_integral_swap (joint_exp_Hamiltonian_integrable hN hp β)]
  apply integral_eq_const
  filter_upwards [sphereLaw_support hN] with x hx
  exact Hamiltonian_sphere_mgf hN hp β x hx

/-- Exact vanishing of the averaged uniform-sphere Hamiltonian. -/
theorem sphere_Hamiltonian_mean_annealed_zero {N p : ℕ} (hN : 0<N) (hp : 1≤p) :
    (∫ J : Disorder N p,∫ x : Vector N,Hamiltonian N p J x ∂sphereLaw N ∂disorderLaw N p)=0 := by
  rw [integral_integral_swap (joint_Hamiltonian_integrable hN hp)]
  simp only [Hamiltonian_mean,integral_zero]


/-- The logarithm lies below its actual tangent line at every positive point. -/
theorem log_tangent_bound {z k : ℝ} (hz : 0<z) (hk : 0<k) :
    Real.log z ≤ Real.log k+(z-k)/k := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hz hk)
  rw [Real.log_div hz.ne' hk.ne'] at hh
  have he : (z-k)/k=z/k-1 := by field_simp
  rw [he]
  linarith only [hh]

/-- Genuine probability log-Jensen, proved by integrating the tangent bound. -/
theorem integral_log_le_log_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {k : ℝ}
    (hf : Integrable f μ) (hlog : Integrable (fun x => Real.log (f x)) μ)
    (hpos : ∀ x,0<f x) (hk : 0<k) (hmean : (∫ x,f x ∂μ)=k) :
    (∫ x,Real.log (f x) ∂μ) ≤ Real.log k := by
  have hi := (integrable_const (Real.log k)).add ((hf.sub (integrable_const k)).div_const k)
  have hh := integral_mono hlog hi (fun x => log_tangent_bound (hpos x) hk)
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  have hi2 : Integrable (fun x => (f x-k)/k) μ := by
    simpa only [Pi.sub_apply] using (hf.sub (integrable_const k)).div_const k
  rw [integral_add (f := fun _ => Real.log k) (g := fun x => (f x-k)/k) (integrable_const _) hi2,
    integral_div,integral_sub (f := f) (g := fun _ => k) hf (integrable_const k),hmean] at hh
  simpa only [integral_const,probReal_univ,one_smul,sub_self,zero_div,add_zero] using hh

theorem log_partition_annealed_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) :
    Integrable (fun J : Disorder N p => Real.log (partitionFunction N p β J)) (disorderLaw N p) := by
  apply ((landscapeNorm_integrable hN hp).const_mul (β*(N : ℝ))).mono'
    ((Real.measurable_log.comp (partition_stronglyMeasurable N p β).measurable).aestronglyMeasurable)
  exact Eventually.of_forall (fun J => by
    simpa only [Real.norm_eq_abs,Function.comp_def] using log_partition_bounds hN hp hβ J)

theorem initialEntropy_annealed_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) : Integrable (initialEntropy N p β) (disorderLaw N p) := by
  have he : initialEntropy N p β=(fun J : Disorder N p => Real.log (partitionFunction N p β J)-
      β*(∫ x : Vector N,Hamiltonian N p J x ∂sphereLaw N)) := by
    funext J
    exact initialEntropy_formula hN hp hβ J
  rw [he]
  exact (log_partition_annealed_integrable hN hp hβ).sub
    ((joint_Hamiltonian_integrable hN hp).integral_prod_left.const_mul β)

/-- Exact annealed initial relative entropy, including the zero mean Hamiltonian. -/
theorem initialEntropy_annealed_eq_log_partition {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) :
    (∫ J : Disorder N p,initialEntropy N p β J ∂disorderLaw N p)=
      ∫ J : Disorder N p,Real.log (partitionFunction N p β J) ∂disorderLaw N p := by
  simp_rw [initialEntropy_formula hN hp hβ]
  rw [integral_sub (log_partition_annealed_integrable hN hp hβ)
      ((joint_Hamiltonian_integrable hN hp).integral_prod_left.const_mul β),
    integral_const_mul,sphere_Hamiltonian_mean_annealed_zero hN hp,mul_zero,sub_zero]

/-- The actual annealed initial entropy is at most beta²*N/2, proved from
Gaussian MGF, spherical Fubini and log-Jensen. No entropy budget is assumed. -/
theorem initialEntropy_annealed_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) :
    (∫ J : Disorder N p,initialEntropy N p β J ∂disorderLaw N p) ≤ β^2*(N : ℝ)/2 := by
  rw [initialEntropy_annealed_eq_log_partition hN hp hβ]
  have hh := integral_log_le_log_mean (partition_annealed_integrable hN hp β)
    (log_partition_annealed_integrable hN hp hβ) (partition_positive hN hp hβ)
    (Real.exp_pos (β^2*(N : ℝ)/2)) (partition_annealed_mean hN hp β)
  simpa only [Real.log_exp] using hh

/-- The quenched normalized initial entropy bound printed in Lemma 5.1. -/
theorem initialEntropy_normalized_quenched {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    0 ≤ initialEntropy N p β J/(N : ℝ) ∧
      initialEntropy N p β J/(N : ℝ) ≤ 2*β*landscapeNorm N p J := by
  refine ⟨div_nonneg (initialEntropy_nonnegative hN hp hβ J) (Nat.cast_nonneg N),?_⟩
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hh := (le_abs_self (initialEntropy N p β J)).trans (initialEntropy_abs_bound hN hp hβ J)
  nlinarith only [hh]

/-- Genuine normalized annealed initial entropy bound beta²/2. -/
theorem initialEntropy_normalized_annealed {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) :
    (∫ J : Disorder N p,initialEntropy N p β J/(N : ℝ) ∂disorderLaw N p) ≤ β^2/2 := by
  rw [integral_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hh := initialEntropy_annealed_bound hN hp hβ
  nlinarith only [hh]

end SphericalAging.SphereGibbsEntropy
