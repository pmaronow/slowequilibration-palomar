-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import SlowEquilibration.SphericalLatitude

@[expose] public section

/-! # Exact weighted-replica and latitude geometry for the stronger plateau

The actual barycenter fluctuation is bounded by the genuine reweighted
two-replica fluctuation. The transverse target and the first/second moment
identity below are deterministic; no pressure or contiguity estimate is
assumed or asserted by this module.
-/

namespace SlowEquilibration.SphericalWeightedReplicaGeometry
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalBarycenter
open scoped Topology InnerProductSpace ContDiff
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- Product support follows from literal support of both replicas. -/
theorem sphereSupported_prod (W : Measure (Vector N)) [IsProbabilityMeasure W]
    (hs : ∀ᵐ u ∂W, ‖u‖^2 = (N : ℝ)) :
    ∀ᵐ z : Vector N × Vector N ∂W.prod W,
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isClosed_eq (continuous_fst.norm.pow 2) continuous_const).measurableSet.inter
      (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).measurableSet)).mpr
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  exact ⟨hx,hy⟩

/-- The genuine overlap deviation has a square-integrable bound under any
sphere-supported replica probability law. -/
theorem overlap_deviation_memLp (hN : 1 ≤ N) (W : Measure (Vector N))
    [IsProbabilityMeasure W] (hs : ∀ᵐ u ∂W, ‖u‖^2 = (N : ℝ)) (q : ℝ) :
    MemLp (fun z : Vector N × Vector N => overlap z.1 z.2-q) 2 (W.prod W) := by
  have hf : Continuous (fun z : Vector N × Vector N => overlap z.1 z.2-q) := by
    unfold overlap
    fun_prop
  apply MemLp.of_bound hf.aestronglyMeasurable (1+|q|)
  filter_upwards [sphereSupported_prod W hs] with z hz
  have hR := abs_le.mpr (overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2)
  simpa only [Real.norm_eq_abs] using (abs_sub (overlap z.1 z.2) q).trans
    (add_le_add hR le_rfl)

/-- Jensen's square bound for the literal overlap mean, with its genuine
replica law rather than an abstract supplied barycenter. -/
theorem overlap_mean_deviation_sq_le (hN : 1 ≤ N) (W : Measure (Vector N))
    [IsProbabilityMeasure W] (hs : ∀ᵐ u ∂W, ‖u‖^2 = (N : ℝ)) (q : ℝ) :
    ((∫ z : Vector N × Vector N, overlap z.1 z.2 ∂W.prod W)-q)^2 ≤
      ∫ z : Vector N × Vector N, (overlap z.1 z.2-q)^2 ∂W.prod W := by
  let f := fun z : Vector N × Vector N => overlap z.1 z.2-q
  have hm := overlap_deviation_memLp hN W hs q
  have hi : Integrable (fun z : Vector N × Vector N => overlap z.1 z.2) (W.prod W) := by
    have h := (overlap_deviation_memLp hN W hs 0).integrable (by norm_num)
    simpa only [sub_zero] using h
  have he : (∫ z, f z ∂W.prod W)=(∫ z : Vector N × Vector N, overlap z.1 z.2 ∂W.prod W)-q := by
    rw [show f=(fun z : Vector N × Vector N => overlap z.1 z.2-q) from rfl,
      integral_sub hi (integrable_const q)]
    simp only [integral_const,probReal_univ,one_smul]
  have hb := SphericalAging.PredictableDriftTime.integral_sq_le_measure_mul_integral_sq
    (W.prod W) f hm
  rw [he] at hb
  simpa only [probReal_univ,one_mul] using hb

/-- The actual source barycenter fluctuation is controlled pointwise by
the exact weighted two-replica overlap fluctuation, at every reference. -/
theorem barycenter_deviation_sq_le (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) (q : ℝ) :
    (‖barycenter β H h x‖^2-q)^2 ≤
      ∫ z : Vector N × Vector N, (overlap z.1 z.2-q)^2
        ∂(weightedLaw β H h x).prod (weightedLaw β H h x) := by
  let _ := weightedLaw_probability hN β hH hh x
  rw [barycenter_norm_sq_eq hN β hH hh x]
  exact overlap_mean_deviation_sq_le hN _ (weightedLaw_support hN β H h x) q

/-- The preceding bound specialized to the manuscript's literal smooth
source observable and finite mixed field. -/
theorem sourceObservable_deviation_sq_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) (D : Disorder N μ.maxDegree) (x : Vector N) (q : ℝ) :
    (‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2-q)^2 ≤
      ∫ z : Vector N × Vector N, (overlap z.1 z.2-q)^2
        ∂(weightedLaw β (fieldOfMixture μ D) (sourceProfile J δ q₁ q₂) x).prod
          (weightedLaw β (fieldOfMixture μ D) (sourceProfile J δ q₁ q₂) x) :=
  barycenter_deviation_sq_le hN β (fieldOfMixture_contDiff μ D).continuous
    (sourceProfile_contDiff J δ q₁ q₂) x q

/-- The deterministic transverse target in source (16.2). -/
def transverseTarget (q : ℝ) : ℝ := q/(1+q)

theorem transverseTarget_mem_Icc {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    transverseTarget q ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 < 1+q := by linarith [hq.1]
  constructor
  · exact div_nonneg hq.1 hd.le
  · exact (div_le_one hd).mpr (by linarith)

/-- The exact scalar identity identifying the spherical plateau. -/
theorem transverseTarget_identity {q : ℝ} (hq : q ≠ -1) :
    q^2+(1-q^2)*transverseTarget q=q := by
  have hd : 1+q ≠ 0 := by intro h; apply hq; linarith
  unfold transverseTarget
  field_simp
  ring

/-- The scalar overlap of two possibly different latitudes. -/
def latitudePairOverlap (r r' t : ℝ) : ℝ :=
  r*r'+Real.sqrt ((1-r^2)*(1-r'^2))*t

theorem latitudePairOverlap_diagonal {q : ℝ} (hq : |q| ≤ 1) (t : ℝ) :
    latitudePairOverlap q q t=q^2+(1-q^2)*t := by
  have hnon : 0 ≤ 1-q^2 := by nlinarith [abs_le.mp hq]
  have hs := Real.sqrt_sq hnon
  rw [pow_two] at hs
  rw [latitudePairOverlap,hs]
  ring

/-- Exact two-latitude geometry, with the actual tangent and ambient
dimensions and the normalization used by the manuscript. -/
theorem overlap_latitude_pair_general {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {r r' : ℝ} (hr : |r| ≤ 1) (hr' : |r'| ≤ 1)
    (x y : Vector n) :
    overlap (latitudeMap u e r x) (latitudeMap u e r' y)=
      latitudePairOverlap r r' (overlap x y) := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hA : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hB : 0 ≤ 1-r'^2 := by nlinarith [abs_le.mp hr']
  have hRatio : 0 ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ) := (div_pos hN hnr).le
  have hscale : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r'^2))=
      (((n+1 : ℕ) : ℝ)/(n : ℝ))*Real.sqrt ((1-r^2)*(1-r'^2)) := by
    rw [← Real.sqrt_mul (mul_nonneg hRatio hA)]
    have heq : (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*
        (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r'^2))=
        (((n+1 : ℕ) : ℝ)/(n : ℝ))^2*((1-r^2)*(1-r'^2)) := by ring
    rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hRatio]
  have he' : ∀ x, inner ℝ u (e x)=0 := fun x => by rw [real_inner_comm,he]
  simp only [overlap,latitudeMap,latitudePairOverlap,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,hu,
    he,he',e.inner_map_map,mul_zero,zero_add,add_zero]
  have hregroup : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r'^2))*
      (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*inner ℝ x y)=
      (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*
        Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r'^2)))*inner ℝ x y := by ring
  rw [hregroup,hscale]
  field_simp

/-- The exact centered second moment is determined by the first and
second moments. These are the primitive quantities obtained from the
two transverse amplitude derivatives in the manuscript. -/
theorem integral_centered_sq_eq {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (t : Ω → ℝ)
    (ht : Integrable t ρ) (ht₂ : Integrable (fun x => (t x)^2) ρ) (t₀ : ℝ) :
    (∫ x, (t x-t₀)^2 ∂ρ)=
      (∫ x, (t x)^2 ∂ρ)-2*t₀*(∫ x, t x ∂ρ)+t₀^2 := by
  have he : (fun x => (t x-t₀)^2)=
      (fun x => (t x)^2-(2*t₀)*t x+t₀^2) := by
    funext x
    ring
  have hsub : Integrable (fun x => (t x)^2-(2*t₀)*t x) ρ :=
    ht₂.sub (ht.const_mul (2*t₀))
  rw [he,integral_add hsub (integrable_const (t₀^2)),
    integral_sub ht₂ (ht.const_mul _),integral_const_mul]
  simp only [integral_const,probReal_univ,one_smul]

/-- At the limiting latitude, the actual spherical overlap variance is
the transverse variance times its exact geometric coefficient. -/
theorem integral_latitude_diagonal_deviation_sq_eq {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (t : Ω → ℝ)
    (ht : Integrable t ρ) (ht₂ : Integrable (fun x => (t x)^2) ρ)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ x, (latitudePairOverlap q q (t x)-q)^2 ∂ρ)=
      (1-q^2)^2*((∫ x, (t x)^2 ∂ρ)-
        2*transverseTarget q*(∫ x, t x ∂ρ)+(transverseTarget q)^2) := by
  have hqabs : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1],hq.2⟩
  have hqne : q ≠ -1 := by linarith [hq.1]
  have hid := transverseTarget_identity hqne
  have he : (fun x => (latitudePairOverlap q q (t x)-q)^2)=
      (fun x => (1-q^2)^2*(t x-transverseTarget q)^2) := by
    funext x
    rw [latitudePairOverlap_diagonal hqabs]
    have hd : q^2+(1-q^2)*t x-q=(1-q^2)*(t x-transverseTarget q) := by
      calc
        q^2+(1-q^2)*t x-q=
            q^2+(1-q^2)*t x-(q^2+(1-q^2)*transverseTarget q) := by rw [hid]
        _=(1-q^2)*(t x-transverseTarget q) := by ring
    rw [hd,mul_pow]
  rw [he,integral_const_mul,integral_centered_sq_eq ρ t ht ht₂]

/-- The primitive first and second transverse moment limits force the
diagonal latitude overlap fluctuation to vanish. This statement leaves
the pressure proof of those two limits explicit and separate. -/
theorem tendsto_latitude_diagonal_fluctuation {ι Ω : Type*} [MeasurableSpace Ω]
    {l : Filter ι} (ρ : ι → Measure Ω) (t : ι → Ω → ℝ)
    [∀ i, IsProbabilityMeasure (ρ i)] (ht : ∀ i, Integrable (t i) (ρ i))
    (ht₂ : ∀ i, Integrable (fun x => (t i x)^2) (ρ i))
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hfirst : Tendsto (fun i => ∫ x, t i x ∂ρ i) l (𝓝 (transverseTarget q)))
    (hsecond : Tendsto (fun i => ∫ x, (t i x)^2 ∂ρ i) l (𝓝 ((transverseTarget q)^2))) :
    Tendsto (fun i => ∫ x, (latitudePairOverlap q q (t i x)-q)^2 ∂ρ i)
      l (𝓝 (0 : ℝ)) := by
  have h := ((hsecond.sub (hfirst.const_mul (2*transverseTarget q))).add_const
    ((transverseTarget q)^2)).const_mul ((1-q^2)^2)
  have hz : (1-q^2)^2*((transverseTarget q)^2-
      (2*transverseTarget q)*transverseTarget q+(transverseTarget q)^2)=0 := by ring
  rw [hz] at h
  convert h using 1
  funext i
  exact integral_latitude_diagonal_deviation_sq_eq (ρ i) (t i) (ht i) (ht₂ i) hq

/-- The varying latitude formula is continuous in all three scalar
coordinates, so simultaneous latitude and transverse limits give the
literal spherical overlap limit. -/
theorem latitudePairOverlap_continuous :
    Continuous (fun z : ℝ × ℝ × ℝ => latitudePairOverlap z.1 z.2.1 z.2.2) := by
  unfold latitudePairOverlap
  fun_prop

theorem tendsto_latitudePairOverlap {ι : Type*} {l : Filter ι} (r r' t : ι → ℝ)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hr : Tendsto r l (𝓝 q)) (hr' : Tendsto r' l (𝓝 q))
    (ht : Tendsto t l (𝓝 (transverseTarget q))) :
    Tendsto (fun i => latitudePairOverlap (r i) (r' i) (t i)) l (𝓝 q) := by
  have h := latitudePairOverlap_continuous.tendsto (q,q,transverseTarget q)
  have he : latitudePairOverlap q q (transverseTarget q)=q := by
    rw [latitudePairOverlap_diagonal (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩)]
    exact transverseTarget_identity (by linarith [hq.1])
  rw [he] at h
  convert h.comp (hr.prodMk_nhds (hr'.prodMk_nhds ht)) using 1
  rfl

end
end SlowEquilibration.SphericalWeightedReplicaGeometry
