-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbs
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators InnerProductSpace

/-- All actual ordered tensor coordinates, with the degree label retained. -/
abbrev Coordinate (N P : ℕ) :=
  (p : Degree P) × SphericalAging.FiniteModel.TensorIndex N p.val.val

abbrev EuclideanDisorder (N P : ℕ) := EuclideanSpace ℝ (Coordinate N P)

def flatDisorder {N P : ℕ} (J : Disorder N P) : Coordinate N P → ℝ :=
  fun k => J k.1 k.2

def euclideanDisorder {N P : ℕ} (J : Disorder N P) : EuclideanDisorder N P :=
  WithLp.toLp 2 (flatDisorder J)

def unpackDisorder {N P : ℕ} (g : EuclideanDisorder N P) : Disorder N P :=
  fun p I => g ⟨p,I⟩

@[simp] theorem unpack_euclideanDisorder {N P : ℕ} (J : Disorder N P) :
    unpackDisorder (euclideanDisorder J)=J := rfl

theorem flatDisorder_measurable (N P : ℕ) : Measurable (flatDisorder (N:=N) (P:=P)) := by
  apply Measurable.of_eval
  intro k
  exact (measurable_pi_apply k.2).comp (measurable_pi_apply k.1)

/-- Flattening is proved to preserve the actual independent Gaussian law;
no isotropic Euclidean disorder law is substituted without identification. -/
theorem flatDisorder_hasLaw (N P : ℕ) :
    HasLaw (flatDisorder (N:=N) (P:=P))
      (Measure.pi (fun _ : Coordinate N P => gaussianReal 0 1)) (disorderLaw N P) := by
  refine ⟨(flatDisorder_measurable N P).aemeasurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (flatDisorder_measurable N P) (MeasurableSet.pi Set.countable_univ (fun k _=>hs k))]
  have hpre : flatDisorder (N:=N) (P:=P) ⁻¹' Set.pi univ s =
      Set.pi univ (fun p : Degree P => Set.pi univ (fun I => s ⟨p,I⟩)) := by
    ext J
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies,flatDisorder]
    change (∀ k : Coordinate N P,J k.1 k.2 ∈ s k) ↔
      ∀ p : Degree P, ∀ I,J p I ∈ s ⟨p,I⟩
    constructor
    · exact fun h p I => h ⟨p,I⟩
    · exact fun h k => h k.1 k.2
  rw [hpre,disorderLaw,Measure.pi_pi]
  simp only [SphericalAging.FiniteModel.disorderLaw,Measure.pi_pi]
  exact (Fintype.prod_sigma (fun k : Coordinate N P => (gaussianReal 0 1) (s k))).symm

theorem euclideanDisorder_hasLaw (N P : ℕ) :
    HasLaw (euclideanDisorder (N:=N) (P:=P))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) (disorderLaw N P) := by
  have hm : Measurable (WithLp.toLp 2 : (Coordinate N P → ℝ) → EuclideanDisorder N P) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable
  exact (hasLaw_map hm.aemeasurable).fun_comp (flatDisorder_hasLaw N P)

/-- The exact coefficient feature vector of the mixed tensor field. -/
def fieldFeature {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) : EuclideanDisorder N P :=
  WithLp.toLp 2 (fun k : Coordinate N P => Real.sqrt (c k.1)*
    SphericalAging.FiniteModel.normalization N k.1.val.val*
    SphericalAging.FiniteModel.tensorMonomial x k.2)

theorem fieldFeature_inner {N P : ℕ} (c : Degree P → ℝ)
    (g : EuclideanDisorder N P) (x : Vector N) :
    inner ℝ g (fieldFeature c x)=field c (unpackDisorder g) x := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,fieldFeature,
    field,blockField,SphericalAging.FiniteModel.Hamiltonian,unpackDisorder]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem fieldFeature_norm_sq {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    ‖fieldFeature c x‖^2=(N:ℝ)*covariancePolynomial c 1 := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,fieldFeature]
  rw [Fintype.sum_sigma]
  unfold covariancePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have heq : (fun I : SphericalAging.FiniteModel.TensorIndex N p.val.val =>
      (Real.sqrt (c p)*SphericalAging.FiniteModel.normalization N p.val.val*
        SphericalAging.FiniteModel.tensorMonomial x I)*
      (Real.sqrt (c p)*SphericalAging.FiniteModel.normalization N p.val.val*
        SphericalAging.FiniteModel.tensorMonomial x I))=
      fun I => c p*SphericalAging.FiniteModel.normalization N p.val.val^2*
        (SphericalAging.FiniteModel.tensorMonomial x I*SphericalAging.FiniteModel.tensorMonomial x I) := by
    funext I
    calc
      _ = (Real.sqrt (c p))^2*SphericalAging.FiniteModel.normalization N p.val.val^2*
        (SphericalAging.FiniteModel.tensorMonomial x I*SphericalAging.FiniteModel.tensorMonomial x I) := by ring
      _ = _ := by rw [Real.sq_sqrt (hc p)]
  change (∑ I, ((fun I : SphericalAging.FiniteModel.TensorIndex N p.val.val =>
      (Real.sqrt (c p)*SphericalAging.FiniteModel.normalization N p.val.val*
        SphericalAging.FiniteModel.tensorMonomial x I)*
      (Real.sqrt (c p)*SphericalAging.FiniteModel.normalization N p.val.val*
        SphericalAging.FiniteModel.tensorMonomial x I)) I))= _
  rw [heq,←Finset.mul_sum,SphericalAging.FiniteModel.tensorMonomial_gram,
    real_inner_self_eq_norm_sq,hx]
  have hn : SphericalAging.FiniteModel.normalization N p.val.val^2*(N:ℝ)^p.val.val=(N:ℝ) := by
    rw [SphericalAging.FiniteModel.normalization_sq N p.val.val
      (lt_of_lt_of_le Nat.zero_lt_one hN)]
    have h := SphericalAging.FiniteModel.dimension_covariance_scale N p.val.val
      (lt_of_lt_of_le Nat.zero_lt_one hN) (by omega : 1 ≤ p.val.val) (N:ℝ)
    have hne : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [div_self hne,one_pow,mul_one] using h
  simp only [one_pow,mul_one]
  calc
    _ = c p*(SphericalAging.FiniteModel.normalization N p.val.val^2*(N:ℝ)^p.val.val) := by ring
    _ = _ := by rw [hn];ring

theorem fieldFeature_norm {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    ‖fieldFeature c x‖=Real.sqrt ((N:ℝ)*covariancePolynomial c 1) := by
  rw [←fieldFeature_norm_sq hN c hc x hx,Real.sqrt_sq (norm_nonneg _)]

/-- The uniform field difference bound has exactly the dimension-sqrt
Lipschitz constant used by the manuscript's pressure concentration proof. -/
theorem field_euclidean_difference_bound {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (g h : EuclideanDisorder N P)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    |field c (unpackDisorder g) x-field c (unpackDisorder h) x| ≤
      Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h := by
  rw [←fieldFeature_inner,←fieldFeature_inner,←inner_sub_left]
  have hn := abs_real_inner_le_norm (g-h) (fieldFeature c x)
  rw [fieldFeature_norm hN c hc x hx] at hn
  simpa only [dist_eq_norm,mul_comm] using hn

theorem partition_euclidean_comparison {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β)
    (g h : EuclideanDisorder N P) :
    partition N β (field c (unpackDisorder g)) ≤
      Real.exp (β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h)*
        partition N β (field c (unpackDisorder h)) := by
  have hg := partition_integrand_integrable hN β (field_contDiff c (unpackDisorder g)).continuous
  have hh := partition_integrand_integrable hN β (field_contDiff c (unpackDisorder h)).continuous
  have hb : (fun x : Vector N => Real.exp (β*field c (unpackDisorder g) x)) ≤ᵐ[sphereLaw N]
      fun x => Real.exp (β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h)*
        Real.exp (β*field c (unpackDisorder h) x) := by
    filter_upwards [sphereLaw_support hN] with x hx
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hf := field_euclidean_difference_bound hN c hc g h x hx
    have hlt := mul_le_mul_of_nonneg_left
      ((le_abs_self (field c (unpackDisorder g) x-field c (unpackDisorder h) x)).trans hf) hβ
    linarith
  have hi := integral_mono_ae hg (hh.const_mul _) hb
  simpa only [integral_const_mul,partition] using hi

def logPartitionEuclidean {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (g : EuclideanDisorder N P) : ℝ := Real.log (partition N β (field c (unpackDisorder g)))

theorem logPartitionEuclidean_sub_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β)
    (g h : EuclideanDisorder N P) :
    logPartitionEuclidean c β g-logPartitionEuclidean c β h ≤
      β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h := by
  have hZg := partition_pos hN β (field_contDiff c (unpackDisorder g)).continuous
  have hZh := partition_pos hN β (field_contDiff c (unpackDisorder h)).continuous
  have hz := Real.log_le_log hZg (partition_euclidean_comparison hN c hc hβ g h)
  rw [Real.log_mul (Real.exp_pos _).ne' hZh.ne',Real.log_exp] at hz
  unfold logPartitionEuclidean
  linarith

/-- The pressure observable has the exact √N Lipschitz constant, derived
from the actual feature vector and partition integral. -/
theorem logPartitionEuclidean_lipschitz {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β) :
    LipschitzWith (β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)).toNNReal
      (logPartitionEuclidean (N:=N) c β) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.dist_eq,Real.coe_toNNReal _ (mul_nonneg hβ (Real.sqrt_nonneg _))]
  apply abs_le.mpr
  refine ⟨?_,logPartitionEuclidean_sub_le hN c hc hβ g h⟩
  have hh := logPartitionEuclidean_sub_le hN c hc hβ h g
  rw [dist_comm h g] at hh
  linarith

/-- Two-sided concentration of the actual spherical log partition,
with the manuscript's Gaussian constant and literal disorder expectation. -/
theorem logPartition_concentration {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) :
    disorderLaw N P {J | |Real.log (partition N β (field c J))-
        (∫ K,Real.log (partition N β (field c K)) ∂disorderLaw N P)| > s} ≤
      ENNReal.ofReal (2*Real.exp (-s^2/(2*β^2*(N:ℝ)*covariancePolynomial c 1))) := by
  let F := logPartitionEuclidean (N:=N) c β
  let L : ℝ := β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hL : 0 < L := mul_pos hβ (Real.sqrt_pos.mpr (mul_pos hNr hcov))
  have hLip : LipschitzWith L.toNNReal F := logPartitionEuclidean_lipschitz hN c hc hβ.le
  have hlaw := euclideanDisorder_hasLaw N P
  have hmean : (∫ J : Disorder N P,Real.log (partition N β (field c J)) ∂disorderLaw N P)=
      ∫ g,F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P) := by
    exact hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have h := SYK.euclidean_lipschitz_gaussian_concentration F L s hL hs hLip
  have hset : MeasurableSet {g : EuclideanDisorder N P |
      |F g-(∫ y,F y ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P))| > s} :=
    (isOpen_lt continuous_const (hLip.continuous.sub continuous_const).abs).measurableSet
  nth_rw 1 [←hlaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at h
  have heq : L^2=β^2*(N:ℝ)*covariancePolynomial c 1 := by
    dsimp [L]
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hcov.le)]
    ring
  rw [hmean]
  simpa only [Set.preimage_ofPred_eq,F,logPartitionEuclidean,unpack_euclideanDisorder,heq,mul_assoc] using h

end
end SlowEquilibration.SphericalModel
