module

public import SphericalAging.VectorBrownian
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

/-!
# The actual uniform spherical initial distribution and annealed sample space

The initial point is the radial normalization of a genuine standard Euclidean
Gaussian. Rotation invariance is proved by transport of the actual Gaussian
law. Initial state, ordered disorder and all Brownian paths are independent
coordinates of one explicit product probability space.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal

namespace SphericalAging.SphereInitialLaw
open FiniteModel

/-- Actual standard Euclidean Gaussian law. -/
@[expose] def gaussianLaw (N : ℕ) : Measure (Vector N) := stdGaussian (Vector N)

instance gaussianLaw_probability (N : ℕ) : IsProbabilityMeasure (gaussianLaw N) := by
  unfold gaussianLaw
  infer_instance

/-- Radial normalization onto the sphere of squared radius `N`. -/
@[expose] def normalize (N : ℕ) (x : Vector N) : Vector N := (Real.sqrt N / ‖x‖) • x

theorem normalize_measurable (N : ℕ) : Measurable (normalize N) := by
  unfold normalize
  fun_prop

/-- The canonical rotation-invariant probability law on the manuscript's sphere. -/
@[expose] def sphereLaw (N : ℕ) : Measure (Vector N) := (gaussianLaw N).map (normalize N)

instance sphereLaw_probability (N : ℕ) : IsProbabilityMeasure (sphereLaw N) := by
  unfold sphereLaw
  infer_instance

theorem gaussian_coordinate_hasLaw {N : ℕ} (i : Fin N) :
    HasLaw (fun x : Vector N => x i) (gaussianReal 0 1) (gaussianLaw N) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianLaw,← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (Function.eval i)=_
  exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).map_eq

theorem gaussian_ne_zero_ae {N : ℕ} (hN : 1 ≤ N) : ∀ᵐ x ∂gaussianLaw N, x ≠ 0 := by
  let i : Fin N := ⟨0,by omega⟩
  have ha : ∀ᵐ r ∂gaussianReal 0 1, r ≠ 0 := by
    apply (gaussianReal_absolutelyContinuous 0 (v := 1) one_ne_zero).ae_le
    change ∀ᵐ r : ℝ ∂volume, r ≠ 0
    rw [ae_iff]
    simpa using (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))
  have hb := ((gaussian_coordinate_hasLaw i).ae_iff (by fun_prop)).mpr ha
  filter_upwards [hb] with x hx
  intro he
  exact hx (by rw [he]; rfl)

theorem normalize_norm {N : ℕ} (x : Vector N) (hx : x ≠ 0) :
    ‖normalize N x‖=Real.sqrt N := by
  rw [normalize,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)

theorem normalize_norm_sq {N : ℕ} (x : Vector N) (hx : x ≠ 0) :
    ‖normalize N x‖^2=(N : ℝ) := by
  rw [normalize_norm x hx,Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Exact support on the manuscript sphere, with no support premise. -/
theorem sphereLaw_norm_ae {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂sphereLaw N, ‖x‖=Real.sqrt N := by
  rw [sphereLaw]
  apply (ae_map_iff (normalize_measurable N).aemeasurable ((measurableSet_singleton (Real.sqrt (N : ℝ))).preimage measurable_norm)).mpr
  filter_upwards [gaussian_ne_zero_ae hN] with x hx
  exact normalize_norm x hx

theorem sphereLaw_support {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂sphereLaw N, ‖x‖^2=(N : ℝ) := by
  filter_upwards [sphereLaw_norm_ae hN] with x hx
  rw [hx,Real.sq_sqrt (Nat.cast_nonneg N)]

theorem normalize_equivariant {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) :
    normalize N (U x)=U (normalize N x) := by
  simp [normalize]

/-- Genuine invariance under every orthogonal transformation. -/
theorem sphereLaw_rotation_invariant {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (sphereLaw N).map U=sphereLaw N := by
  have he : U ∘ normalize N=normalize N ∘ U := by
    funext x
    exact (normalize_equivariant U x).symm
  rw [sphereLaw,Measure.map_map (by fun_prop) (normalize_measurable N),he,
    ← Measure.map_map (normalize_measurable N) (by fun_prop)]
  rw [show (gaussianLaw N).map U=gaussianLaw N from stdGaussian_map U]

/-- Every finite or infinite Lp exponent is available from the exact sphere norm. -/
theorem sphereLaw_memLp {N : ℕ} (hN : 1 ≤ N) (q : ℝ≥0∞) :
    MemLp (id : Vector N → Vector N) q (sphereLaw N) :=
  MemLp.of_bound (by fun_prop) (Real.sqrt N) ((sphereLaw_norm_ae hN).mono (fun _ hx => hx.le))

/-- Actual annealed sample space: initial state, ordered tensor and independent Brownian paths. -/
@[expose] abbrev Sample (N p : ℕ) := VectorBrownian.BackgroundSpace (VectorBrownian.ModelBackground N p) N

@[expose] def law (N p : ℕ) : Measure (Sample N p) :=
  VectorBrownian.backgroundLaw (VectorBrownian.modelBackgroundLaw (sphereLaw N) p) N

instance law_probability (N p : ℕ) : IsProbabilityMeasure (law N p) := by
  unfold law
  infer_instance

@[expose] abbrev filtration (N p : ℕ) := VectorBrownian.backgroundFiltration (VectorBrownian.ModelBackground N p) N

@[expose] def initial {N p : ℕ} (ω : Sample N p) : Vector N := ω.1.1

@[expose] def disorder {N p : ℕ} (ω : Sample N p) : Disorder N p := ω.1.2

@[expose] def paths {N p : ℕ} (ω : Sample N p) : VectorBrownian.Space N := ω.2

@[fun_prop] theorem initial_measurable (N p : ℕ) : Measurable (initial : Sample N p → Vector N) :=
  measurable_fst.comp measurable_fst

@[fun_prop] theorem disorder_measurable (N p : ℕ) : Measurable (disorder : Sample N p → Disorder N p) :=
  measurable_snd.comp measurable_fst

@[fun_prop] theorem paths_measurable (N p : ℕ) : Measurable (paths : Sample N p → VectorBrownian.Space N) :=
  measurable_snd

/-- The actual independent full-vector filtered Brownian driver. -/
@[expose] def driver (N p : ℕ) : HardSphereDynamics.BrownianDriver N (law N p) (filtration N p) :=
  VectorBrownian.modelDriver (sphereLaw N) p

theorem initial_hasLaw (N p : ℕ) : HasLaw (initial : Sample N p → Vector N) (sphereLaw N) (law N p) :=
  VectorBrownian.model_initial_hasLaw (sphereLaw N) p

theorem disorder_hasLaw (N p : ℕ) : HasLaw (disorder : Sample N p → Disorder N p) (disorderLaw N p) (law N p) :=
  VectorBrownian.model_disorder_hasLaw (sphereLaw N) p

theorem paths_hasLaw (N p : ℕ) : HasLaw (paths : Sample N p → VectorBrownian.Space N)
    (VectorBrownian.law N) (law N p) := measurePreserving_snd.hasLaw

/-- Initial sphere support is proved under the complete annealed model law. -/
theorem initial_sphere_ae {N p : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ ω ∂law N p, ‖initial ω‖^2=(N : ℝ) :=
  ((initial_hasLaw N p).ae_iff (by fun_prop)).mpr (sphereLaw_support hN)

theorem initial_memLp {N p : ℕ} (hN : 1 ≤ N) (q : ℝ≥0∞) :
    MemLp (initial : Sample N p → Vector N) q (law N p) :=
  (initial_hasLaw N p).memLp (sphereLaw_memLp hN q)

theorem initial_known_at_zero (N p : ℕ) :
    StronglyMeasurable[filtration N p 0] (initial : Sample N p → Vector N) :=
  VectorBrownian.model_initial_known_at_zero

theorem disorder_known_at_zero (N p : ℕ) :
    StronglyMeasurable[filtration N p 0] (disorder : Sample N p → Disorder N p) :=
  VectorBrownian.model_disorder_known_at_zero

/-- Initial state and disorder are independent under the actual full model law. -/
theorem initial_disorder_independent (N p : ℕ) :
    IndepFun (initial : Sample N p → Vector N) (disorder : Sample N p → Disorder N p) (law N p) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
  rw [(initial_hasLaw N p).map_eq,(disorder_hasLaw N p).map_eq]
  change (law N p).map (Prod.fst : Sample N p → VectorBrownian.ModelBackground N p)=_
  exact measurePreserving_fst.map_eq

/-- The whole joint initial/disorder background is independent of all Brownian paths. -/
theorem background_paths_independent (N p : ℕ) :
    IndepFun (fun ω : Sample N p => (initial ω,disorder ω)) paths (law N p) := by
  exact indepFun_prod measurable_id measurable_id

/-- Strong independence: the initial state is independent of the joint disorder and entire noise. -/
theorem initial_disorderPaths_independent (N p : ℕ) :
    IndepFun (initial : Sample N p → Vector N)
      (fun ω : Sample N p => (disorder ω,paths ω)) (law N p) := by
  have ha : HasLaw (fun ω : Sample N p => (initial ω,(disorder ω,paths ω)))
      ((sphereLaw N).prod ((disorderLaw N p).prod (VectorBrownian.law N))) (law N p) :=
    (measurePreserving_prodAssoc (sphereLaw N) (disorderLaw N p) (VectorBrownian.law N)).hasLaw
  have hs : HasLaw (fun ω : Sample N p => (disorder ω,paths ω))
      ((disorderLaw N p).prod (VectorBrownian.law N)) (law N p) :=
    measurePreserving_snd.hasLaw.comp ha
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
  rw [ha.map_eq,(initial_hasLaw N p).map_eq,hs.map_eq]

end SphericalAging.SphereInitialLaw
