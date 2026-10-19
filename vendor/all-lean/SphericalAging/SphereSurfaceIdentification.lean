module

public import SphericalAging.SphereInitialLaw
public import Mathlib.MeasureTheory.Integral.Pi

public section

/-! Exact surface-measure identification of the normalized Gaussian initial point. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Metric
open scoped InnerProductSpace ENNReal
namespace SphericalAging.SphereSurfaceIdentification
open FiniteModel SphereInitialLaw

@[expose] def productDensity (N : ℕ) (x : Fin N → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

@[expose] def radialDensity (N : ℕ) (r : ℝ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹^N*Real.exp (-r^2/2)

theorem productDensity_nonnegative (N : ℕ) (x : Fin N → ℝ) : 0 ≤ productDensity N x :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

@[fun_prop] theorem productDensity_measurable (N : ℕ) : Measurable (productDensity N) := by
  unfold productDensity
  fun_prop

@[fun_prop] theorem radialDensity_measurable (N : ℕ) : Measurable (radialDensity N) := by
  unfold radialDensity
  fun_prop

theorem productDensity_integrable (N : ℕ) : Integrable (productDensity N) (volume : Measure (Fin N → ℝ)) := by
  exact Integrable.fintype_prod (fun _ : Fin N => integrable_gaussianPDFReal 0 1)

/-- Actual finite independent Gaussian product has its genuine product density. -/
theorem gaussian_pi_density (N : ℕ) :
    Measure.pi (fun _ : Fin N => gaussianReal 0 1)=
      (volume : Measure (Fin N → ℝ)).withDensity (fun x => ENNReal.ofReal (productDensity N x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal ((productDensity_integrable N).restrict)
    (Filter.Eventually.of_forall (productDensity_nonnegative N))]
  change ENNReal.ofReal (∫ x, ∏ i, gaussianPDFReal 0 1 (x i) ∂(volume.restrict (univ.pi s)))=_
  rw [show (volume : Measure (Fin N → ℝ))=Measure.pi (fun _ : Fin N => (volume : Measure ℝ)) from rfl,
    Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
  simp_rw [gaussianReal_apply_eq_integral 0 (v := 1) one_ne_zero]
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact integral_nonneg (gaussianPDFReal_nonneg _ _)

/-- The product density depends only on the Euclidean radius, with its exact normalization. -/
theorem productDensity_eq_radial (N : ℕ) (x : Vector N) :
    productDensity N (WithLp.ofLp x)=radialDensity N ‖x‖ := by
  unfold productDensity radialDensity gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero]
  rw [Finset.prod_mul_distrib,← Real.exp_sum]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  simp only [← Finset.sum_div,← Finset.sum_neg_distrib]

/-- Genuine standard Euclidean Gaussian density against Euclidean Haar volume. -/
theorem gaussianLaw_density (N : ℕ) :
    gaussianLaw N=(volume : Measure (Vector N)).withDensity
      (fun x => ENNReal.ofReal (radialDensity N ‖x‖)) := by
  rw [gaussianLaw,← map_pi_eq_stdGaussian,gaussian_pi_density]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,withDensity_apply _ (hs.preimage (by fun_prop)),
    withDensity_apply _ hs]
  have hm := (PiLp.volume_preserving_toLp (Fin N)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurableEmbedding
    (fun x : Vector N => ENNReal.ofReal (radialDensity N ‖x‖)) s
  convert hm using 1
  congr 1
  ext x
  exact congrArg ENNReal.ofReal (productDensity_eq_radial N (WithLp.toLp 2 x))

/-- Actual Euclidean surface measure on the unit sphere. -/
@[expose] def unitSurface (N : ℕ) : Measure (sphere (0 : Vector N) 1) :=
  (volume : Measure (Vector N)).toSphere

/-- The genuine radial measure in polar coordinates. -/
@[expose] def radialMeasure (N : ℕ) : Measure (Ioi (0 : ℝ)) :=
  Measure.volumeIoiPow (Module.finrank ℝ (Vector N)-1)

instance radialMeasure_sigmaFinite (N : ℕ) : SigmaFinite (radialMeasure N) := by
  unfold radialMeasure
  infer_instance

instance unitSurface_finite (N : ℕ) : IsFiniteMeasure (unitSurface N) := by
  unfold unitSurface
  infer_instance

/-- The actual Gaussian law in genuine surface/radius polar coordinates. -/
theorem gaussian_polar_lintegral {N : ℕ} (hN : 1 ≤ N) (f : Vector N → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂gaussianLaw N =
      ∫⁻ θ : sphere (0 : Vector N) 1,
        ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (radialDensity N r)*f (r.1 • θ.1)
          ∂radialMeasure N ∂unitSurface N := by
  letI : NeZero N := ⟨by omega⟩
  let H := homeomorphUnitSphereProd (Vector N)
  have hm := (volume : Measure (Vector N)).measurePreserving_homeomorphUnitSphereProd
  rw [gaussianLaw_density,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  calc
    _ = ∫⁻ x : ({0}ᶜ : Set (Vector N)),
        ENNReal.ofReal (radialDensity N ‖x.1‖)*f x.1 ∂((volume : Measure (Vector N)).comap (↑)) := by
      symm
      exact (lintegral_subtype_comap (measurableSet_singleton (0 : Vector N)).compl
        (fun x : Vector N => ENNReal.ofReal (radialDensity N ‖x‖)*f x)).trans (by rw [restrict_compl_singleton]; rfl)
    _ = ∫⁻ q : sphere (0 : Vector N) 1 × Ioi (0 : ℝ),
        ENNReal.ofReal (radialDensity N q.2)*f (q.2.1 • q.1.1)
          ∂((unitSurface N).prod (radialMeasure N)) := by
      dsimp [unitSurface,radialMeasure]
      rw [← hm.lintegral_comp_emb (Homeomorph.measurableEmbedding _) ]
      apply lintegral_congr
      intro x
      simp only [homeomorphUnitSphereProd_apply_fst_coe,homeomorphUnitSphereProd_apply_snd_coe,smul_smul]
      have hx : (x.1 : Vector N) ≠ 0 := x.2
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
    _ = _ := lintegral_prod _ (by fun_prop)

/-- On polar coordinates, radial normalization keeps precisely the angular coordinate. -/
theorem normalize_polar {N : ℕ} (θ : sphere (0 : Vector N) 1) (r : Ioi (0 : ℝ)) :
    normalize N (r.1 • θ.1)=Real.sqrt N • θ.1 := by
  have hθ : ‖θ.1‖=1 := by simpa only [mem_sphere_zero_iff_norm] using θ.2
  rw [SphereInitialLaw.normalize,norm_smul,Real.norm_eq_abs,abs_of_pos r.2,hθ,mul_one,smul_smul,
    div_mul_cancel₀ _ r.2.ne']

/-- Actual radius-integrated Gaussian density, without evaluating its gamma integral. -/
@[expose] def radialMass (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (radialDensity N r) ∂radialMeasure N

/-- The canonical spherical law is an explicit multiple of Euclidean surface measure. -/
theorem sphereLaw_surface_multiple {N : ℕ} (hN : 1 ≤ N) :
    sphereLaw N=radialMass N • (unitSurface N).map (fun θ => Real.sqrt N • θ.1) := by
  apply Measure.ext
  intro s hs
  rw [sphereLaw,Measure.map_apply (normalize_measurable N) hs]
  have hone : (gaussianLaw N) (normalize N ⁻¹' s)=
      ∫⁻ x in normalize N ⁻¹' s, (1 : ℝ≥0∞) ∂gaussianLaw N := by simp
  rw [hone]
  rw [← lintegral_indicator (hs.preimage (normalize_measurable N))]
  rw [gaussian_polar_lintegral hN _ (measurable_const.indicator (hs.preimage (normalize_measurable N)))]
  have hi (θ : sphere (0 : Vector N) 1) :
      (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (radialDensity N r)*
        (normalize N ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) (r.1 • θ.1) ∂radialMeasure N) =
      radialMass N * s.indicator (fun _ => (1 : ℝ≥0∞)) (Real.sqrt N • θ.1) := by
    by_cases hθ : Real.sqrt N • θ.1 ∈ s
    · have he (r : Ioi (0 : ℝ)) : (normalize N ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) (r.1 • θ.1)=1 := by
        apply indicator_of_mem
        simpa only [mem_preimage,normalize_polar] using hθ
      simp_rw [he,mul_one]
      rw [indicator_of_mem hθ,mul_one]
      rfl
    · have he (r : Ioi (0 : ℝ)) : (normalize N ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) (r.1 • θ.1)=0 := by
        apply indicator_of_notMem
        simpa only [mem_preimage,normalize_polar] using hθ
      simp_rw [he,mul_zero]
      rw [indicator_of_notMem hθ,mul_zero]
      simp
  simp_rw [hi]
  rw [lintegral_const_mul _ (by fun_prop),Measure.smul_apply,Measure.map_apply (by fun_prop) hs]
  congr 1
  have he : (fun θ : sphere (0 : Vector N) 1 => s.indicator (fun _ => (1 : ℝ≥0∞)) (Real.sqrt N • θ.1)) =
      ((fun θ : sphere (0 : Vector N) 1 => Real.sqrt N • θ.1) ⁻¹' s).indicator (fun _ => 1) := by
    rfl
  rw [he,lintegral_indicator (hs.preimage (by fun_prop))]
  simp

/-- Probability normalization determines the genuine surface normalization exactly. -/
theorem radialMass_eq_surface_inv {N : ℕ} (hN : 1 ≤ N) :
    radialMass N=((unitSurface N) univ)⁻¹ := by
  have hm := congrArg (fun μ : Measure (Vector N) => μ univ) (sphereLaw_surface_multiple hN)
  simp only [measure_univ,Measure.smul_apply,smul_eq_mul] at hm
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at hm
  simp only [preimage_univ] at hm
  exact ENNReal.eq_inv_of_mul_eq_one_left hm.symm

/-- Literal normalized Euclidean surface measure, scaled to the manuscript sphere. -/
@[expose] def normalizedSurfaceLaw (N : ℕ) : Measure (Vector N) :=
  (((unitSurface N) univ)⁻¹ • unitSurface N).map (fun θ => Real.sqrt N • θ.1)

/-- Exact identification with normalized Euclidean surface measure. -/
theorem sphereLaw_eq_normalizedSurface {N : ℕ} (hN : 1 ≤ N) :
    sphereLaw N=normalizedSurfaceLaw N := by
  rw [sphereLaw_surface_multiple hN,radialMass_eq_surface_inv hN,normalizedSurfaceLaw,
    Measure.map_smul _ (by fun_prop)]

end SphericalAging.SphereSurfaceIdentification
