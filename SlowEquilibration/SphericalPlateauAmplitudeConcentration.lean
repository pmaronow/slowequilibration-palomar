-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFeatureBounds
public import SlowEquilibration.GaussianPerturbationFluctuation
public import SlowEquilibration.SphericalLatitudePolynomialMesh

@[expose] public section

/-! # Sampled concentration of the literal perturbed Gaussian bank

Both the Gaussian Lipschitz constant and the latitude continuity modulus
are derived from the actual flattened tensor features.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel GaussianSpinInterpolation
open scoped Topology BigOperators RealInnerProductSpace ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def amplitudeLatitudeLogPartition (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ)
    (D : BankDisorder n μ) : ℝ :=
  Real.log (partitionAgainst (latitudeLaw x (latitudeFrameAt x) r) β
    (amplitudeField μ x (latitudeFrameAt x) p₀ s D))

def amplitudeLatitudeCenteredLogPartition (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ)
    (D : BankDisorder n μ) : ℝ :=
  amplitudeLatitudeLogPartition μ β x p₀ s r D-
    ∫ E,amplitudeLatitudeLogPartition μ β x p₀ s r E ∂bankLaw n μ

def amplitudeLatitudeModulusScale (n : ℕ) (μ : FiniteMixture) (β : ℝ) : ℝ :=
  4*|β| *Real.sqrt (μ.xi1 1)*Real.sqrt (((n+1 : ℕ) : ℝ))

theorem amplitudeLatitudeModulusScale_nonneg (n : ℕ) (μ : FiniteMixture) (β : ℝ) :
    0≤amplitudeLatitudeModulusScale n μ β := by
  unfold amplitudeLatitudeModulusScale
  positivity

theorem amplitudeLatitudeLogPartition_eq_gaussian (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ)
    (w : EuclideanBank n μ) :
    amplitudeLatitudeLogPartition μ β x p₀ s r (unpackBankCLM n μ w)=
      logPartition (sphereLaw n)
        (fun u => β • amplitudeLatitudeBankLinear μ x (latitudeFrameAt x) p₀ s r u) w := by
  unfold amplitudeLatitudeLogPartition logPartition
  rw [← amplitudeLatitude_gaussianMoment_eq_partition]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun u => by
    simp only [weight,map_smul,smul_apply,smul_eq_mul]

theorem amplitudeLatitudeLogPartition_gaussian_lipschitz (hn : 1≤n)
    (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) {r : ℝ} (hr : |r|≤1) :
    LipschitzWith (2*|β| *Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)).toNNReal
      (fun w : EuclideanBank n μ => amplitudeLatitudeLogPartition μ β x p₀ s r (unpackBankCLM n μ w)) := by
  have hb : ∀ᵐ u ∂sphereLaw n,
      ‖β • amplitudeLatitudeBankLinear μ x (latitudeFrameAt x) p₀ s r u‖≤
        2*|β| *Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1) := by
    filter_upwards [sphereLaw_support hn] with u hu
    simp only [norm_smul,Real.norm_eq_abs,amplitudeLatitudeBankLinear,innerSL_apply_norm]
    have hf := amplitudeBankFeature_norm_le μ x hx p₀ s hs
      (latitudeMap x (latitudeFrameAt x) r u)
      (latitudeMap_norm_sq hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) hr u hu)
    have hm := mul_le_mul_of_nonneg_left hf (abs_nonneg β)
    simpa only [amplitudeLatitudeBankFeature] using (hm.trans_eq (by ring))
  have hL : Measurable (fun u : Vector n => β • amplitudeLatitudeBankLinear μ x (latitudeFrameAt x) p₀ s r u) :=
    ((amplitudeLatitudeBankLinear_continuous μ x (latitudeFrameAt x) p₀ s r).const_smul β).measurable
  have h := GaussianPerturbationFluctuation.logPartition_lipschitz (sphereLaw n) _ hL
    (by positivity : 0≤2*|β| *Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)) hb
  have he : (fun w : EuclideanBank n μ => amplitudeLatitudeLogPartition μ β x p₀ s r (unpackBankCLM n μ w))=
      logPartition (sphereLaw n) (fun u => β • amplitudeLatitudeBankLinear μ x (latitudeFrameAt x) p₀ s r u) :=
    funext (amplitudeLatitudeLogPartition_eq_gaussian μ β x p₀ s r)
  rw [he]
  exact h

theorem amplitudeLatitudeLogPartition_integrable (hn : 1≤n)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) {r : ℝ} (hr : |r|≤1) :
    Integrable (amplitudeLatitudeLogPartition μ β x p₀ s r) (bankLaw n μ) := by
  let L : ℝ := 2*|β| *Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)
  have hL : 0<L := by
    dsimp [L]
    exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hβ.ne'))
      (Real.sqrt_pos.mpr (mul_pos (by positivity) (μ.xi_pos (by norm_num))))
  have hLip := amplitudeLatitudeLogPartition_gaussian_lipschitz hn μ β x hx p₀ s hs hr
  have hi := euclidean_lipschitz_integrable _ L hL hLip
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at hi
  have hh := (actual_bank_flattened_gaussian n μ).integrable_comp hi
  simpa only [Function.comp_def,unpackBank_euclideanBank] using hh

theorem amplitudeLatitudeLogPartition_pressure_concentration (hn : 1≤n)
    (μ : FiniteMixture) {β t : ℝ} (hβ : 0<β) (ht : 0<t) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) {r : ℝ} (hr : |r|≤1) :
    bankLaw n μ {D | t*((n+1 : ℕ) : ℝ)≤|amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D|}≤
      ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1))) := by
  let F : EuclideanBank n μ → ℝ := fun w => amplitudeLatitudeLogPartition μ β x p₀ s r (unpackBankCLM n μ w)
  let L : ℝ := 2*|β| *Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)
  have hL : 0<L := by
    dsimp [L]
    exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hβ.ne'))
      (Real.sqrt_pos.mpr (mul_pos (by positivity) (μ.xi_pos (by norm_num))))
  have hLip := amplitudeLatitudeLogPartition_gaussian_lipschitz hn μ β x hx p₀ s hs hr
  have hlaw := actual_bank_flattened_gaussian n μ
  have hmean : (∫ D,amplitudeLatitudeLogPartition μ β x p₀ s r D ∂bankLaw n μ)=
      ∫ w,F w ∂stdGaussian (EuclideanBank n μ) := by
    simpa only [F,Function.comp_apply,unpackBank_euclideanBank] using
      hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have h := euclidean_lipschitz_gaussian_closed_tail F L (t*((n+1 : ℕ) : ℝ)) hL (by positivity) hLip
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at h
  have hset : MeasurableSet {w : EuclideanBank n μ | t*((n+1 : ℕ) : ℝ)≤
      |F w-(∫ y,F y ∂stdGaussian (EuclideanBank n μ))|} :=
    measurableSet_le measurable_const ((hLip.continuous.sub continuous_const).abs.measurable)
  nth_rw 1 [← hlaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at h
  have hpow : L^2=4*β^2*((n+1 : ℕ) : ℝ)*μ.xi 1 := by
    dsimp [L]
    rw [mul_pow,mul_pow,sq_abs,Real.sq_sqrt (mul_nonneg (by positivity) (μ.xi_pos (by norm_num)).le)]
    ring
  have he : -(t*((n+1 : ℕ) : ℝ))^2/(2*L^2)=-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1) := by
    rw [hpow]
    field_simp
    ring
  rw [he] at h
  simpa only [Set.preimage_ofPred_eq,F,unpackBank_euclideanBank,
    amplitudeLatitudeCenteredLogPartition,hmean] using h


theorem euclideanBank_norm_integrable (n : ℕ) (μ : FiniteMixture) :
    Integrable (fun D : BankDisorder n μ => ‖euclideanBank D‖) (bankLaw n μ) := by
  have hi := GaussianSpinInterpolation.gaussian_norm_integrable (ι := BankCoordinate n μ)
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at hi
  exact (actual_bank_flattened_gaussian n μ).integrable_comp hi

theorem euclideanBank_norm_integral_le (n : ℕ) (μ : FiniteMixture) :
    (∫ D : BankDisorder n μ,‖euclideanBank D‖ ∂bankLaw n μ)≤
      Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ) := by
  have he := (actual_bank_flattened_gaussian n μ).integral_comp
    (f := fun w : EuclideanBank n μ => ‖w‖) (by fun_prop)
  dsimp only [Function.comp_apply] at he
  rw [he]
  simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using
    GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card (BankCoordinate n μ)

theorem euclideanBank_norm_upper_tail (n : ℕ) (μ : FiniteMixture) {a : ℝ} (ha : 0≤a) :
    bankLaw n μ {D | Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+a≤‖euclideanBank D‖}≤
      ENNReal.ofReal (Real.exp (-a^2/2)) := by
  have h := GaussianNormConcentration.standardGaussian_norm_upper_tail (ι := BankCoordinate n μ) ha
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at h
  have hlaw := actual_bank_flattened_gaussian n μ
  rw [← hlaw.map_eq,Measure.map_apply_of_aemeasurable hlaw.aemeasurable
    (measurableSet_le measurable_const (by fun_prop))] at h
  exact h

theorem amplitudeLatitudePartition_eq_sphereIntegral (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ)
    (D : BankDisorder n μ) :
    partitionAgainst (latitudeLaw x (latitudeFrameAt x) r) β
      (amplitudeField μ x (latitudeFrameAt x) p₀ s D)=
    ∫ u,Real.exp (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) r u)) ∂sphereLaw n := by
  unfold partitionAgainst latitudeLaw
  apply integral_map (latitudeMap_continuous x (latitudeFrameAt x) r).measurable.aemeasurable
  exact (Real.continuous_exp.comp
    ((amplitudeField_contDiff μ x (latitudeFrameAt x) p₀ s D).continuous.const_mul β)).aestronglyMeasurable

theorem amplitudeLatitude_field_dist_le (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) (D : BankDisorder n μ)
    {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1) (u : Vector n) (hu : ‖u‖^2=(n : ℝ)) :
    |β*amplitudeField μ x (latitudeFrameAt x) p₀ s D (latitudeMap x (latitudeFrameAt x) r u)-
      β*amplitudeField μ x (latitudeFrameAt x) p₀ s D (latitudeMap x (latitudeFrameAt x) q u)|≤
      amplitudeLatitudeModulusScale n μ β*‖euclideanBank D‖*Real.sqrt |r-q| := by
  have he (a : ℝ) : amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) a u)=
      inner ℝ (amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s a u) (euclideanBank D) := by
    have hh := amplitudeBankLinear_apply μ 1 x (latitudeFrameAt x) p₀ s
      (latitudeMap x (latitudeFrameAt x) a u) (euclideanBank D)
    simpa only [amplitudeBankLinear,one_smul,innerSL_apply_apply,unpackBank_euclideanBank,
      one_mul,amplitudeLatitudeBankFeature] using hh.symm
  rw [he r,he q,← mul_sub,← inner_sub_left,abs_mul]
  have hb := amplitudeLatitudeBankFeature_dist_le hn μ x hx p₀ s hs hr hq u hu
  have hh := abs_real_inner_le_norm
    (amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s r u-
      amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s q u) (euclideanBank D)
  have hmul := mul_le_mul_of_nonneg_left
    (hh.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) (abs_nonneg β)
  exact hmul.trans_eq (by unfold amplitudeLatitudeModulusScale;ring)

theorem amplitudeLatitudeLogPartition_sub_le (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) (D : BankDisorder n μ)
    {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1) :
    amplitudeLatitudeLogPartition μ β x p₀ s r D-amplitudeLatitudeLogPartition μ β x p₀ s q D≤
      amplitudeLatitudeModulusScale n μ β*‖euclideanBank D‖*Real.sqrt |r-q| := by
  have hi (a : ℝ) : Integrable (fun u => Real.exp (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) a u))) (sphereLaw n) :=
    partition_integrand_integrable hn β
      ((amplitudeField_contDiff μ x (latitudeFrameAt x) p₀ s D).continuous.comp
        (latitudeMap_continuous x (latitudeFrameAt x) a))
  have hcomp : partitionAgainst (latitudeLaw x (latitudeFrameAt x) r) β
      (amplitudeField μ x (latitudeFrameAt x) p₀ s D)≤
      Real.exp (amplitudeLatitudeModulusScale n μ β*‖euclideanBank D‖*Real.sqrt |r-q|)*
      partitionAgainst (latitudeLaw x (latitudeFrameAt x) q) β
        (amplitudeField μ x (latitudeFrameAt x) p₀ s D) := by
    rw [amplitudeLatitudePartition_eq_sphereIntegral,amplitudeLatitudePartition_eq_sphereIntegral,
      ← integral_const_mul]
    apply integral_mono_ae (hi r) ((hi q).const_mul _)
    filter_upwards [sphereLaw_support hn] with u hu
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self _).trans (amplitudeLatitude_field_dist_le hn μ β x hx p₀ s hs D hr hq u hu)
    linarith
  have hp (a : ℝ) (ha : |a|≤1) : 0<partitionAgainst (latitudeLaw x (latitudeFrameAt x) a) β
      (amplitudeField μ x (latitudeFrameAt x) p₀ s D) :=
    partitionAgainst_pos _
      ((latitudeLaw_support hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) ha).mono fun _ hv => hv.1)
      β (amplitudeField_contDiff μ x (latitudeFrameAt x) p₀ s D).continuous
  have hh := Real.log_le_log (hp r hr) hcomp
  rw [Real.log_mul (Real.exp_pos _).ne' (hp q hq).ne',Real.log_exp] at hh
  unfold amplitudeLatitudeLogPartition
  linarith

theorem amplitudeLatitudeLogPartition_dist_le (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) (D : BankDisorder n μ)
    {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1) :
    |amplitudeLatitudeLogPartition μ β x p₀ s r D-amplitudeLatitudeLogPartition μ β x p₀ s q D|≤
      amplitudeLatitudeModulusScale n μ β*‖euclideanBank D‖*Real.sqrt |r-q| := by
  apply abs_le.mpr
  have hh := amplitudeLatitudeLogPartition_sub_le hn μ β x hx p₀ s hs D hq hr
  rw [abs_sub_comm q r] at hh
  exact ⟨by linarith,amplitudeLatitudeLogPartition_sub_le hn μ β x hx p₀ s hs D hr hq⟩

theorem amplitudeLatitudeMeanLogPartition_sub_le (hn : 1≤n) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0<β) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2)
    {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1) :
    (∫ D,amplitudeLatitudeLogPartition μ β x p₀ s r D ∂bankLaw n μ)-
      (∫ D,amplitudeLatitudeLogPartition μ β x p₀ s q D ∂bankLaw n μ)≤
      amplitudeLatitudeModulusScale n μ β*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)*Real.sqrt |r-q| := by
  rw [← integral_sub (amplitudeLatitudeLogPartition_integrable hn μ hβ x hx p₀ s hs hr)
    (amplitudeLatitudeLogPartition_integrable hn μ hβ x hx p₀ s hs hq)]
  calc
    _ ≤ ∫ D : BankDisorder n μ,amplitudeLatitudeModulusScale n μ β*‖euclideanBank D‖*Real.sqrt |r-q| ∂bankLaw n μ := by
      apply integral_mono
        ((amplitudeLatitudeLogPartition_integrable hn μ hβ x hx p₀ s hs hr).sub
          (amplitudeLatitudeLogPartition_integrable hn μ hβ x hx p₀ s hs hq))
        (((euclideanBank_norm_integrable n μ).const_mul _).mul_const _)
      exact fun D => amplitudeLatitudeLogPartition_sub_le hn μ β x hx p₀ s hs D hr hq
    _ ≤ _ := by
      rw [integral_mul_const,integral_const_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (euclideanBank_norm_integral_le n μ)
          (amplitudeLatitudeModulusScale_nonneg n μ β)) (Real.sqrt_nonneg _)

theorem amplitudeLatitudeCenteredLogPartition_dist_le (hn : 1≤n) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0<β) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) (D : BankDisorder n μ)
    {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1) :
    |amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D-
      amplitudeLatitudeCenteredLogPartition μ β x p₀ s q D|≤
      amplitudeLatitudeModulusScale n μ β*(‖euclideanBank D‖+
        Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ))*Real.sqrt |r-q| := by
  have hf := amplitudeLatitudeLogPartition_dist_le hn μ β x hx p₀ s hs D hr hq
  have hm := amplitudeLatitudeMeanLogPartition_sub_le hn μ hβ x hx p₀ s hs hr hq
  have hm' := amplitudeLatitudeMeanLogPartition_sub_le hn μ hβ x hx p₀ s hs hq hr
  rw [abs_sub_comm q r] at hm'
  apply abs_le.mpr
  unfold amplitudeLatitudeCenteredLogPartition
  constructor <;> nlinarith [abs_le.mp hf]


/-- Literal continuum concentration with the actual Gaussian norm tail and a
finite collection of actual bank latitude tails. -/
theorem amplitudeLatitude_uniform_concentration_finite_mesh {k : ℕ} (hn : 1≤n) (hk : 1≤k)
    (μ : FiniteMixture) {β t z a b : ℝ} (hβ : 0<β) (ht : 0<t) (hz : 0≤z)
    (ha : -1≤a) (hb : b≤1) (hab : a≤b)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) :
    bankLaw n μ {D | ∃ q∈Icc a b,
      t*((n+1 : ℕ) : ℝ)+amplitudeLatitudeModulusScale n μ β*
        (2*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+z)*Real.sqrt ((b-a)/(k : ℝ))≤
          |amplitudeLatitudeCenteredLogPartition μ β x p₀ s q D|}≤
      ENNReal.ofReal (Real.exp (-z^2/2))+
        ((k+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal
          (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1))) := by
  classical
  let A : Set (BankDisorder n μ) :=
    {D | Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+z≤‖euclideanBank D‖}
  let B : Fin (k+1) → Set (BankDisorder n μ) := fun i =>
    {D | t*((n+1 : ℕ) : ℝ)≤|amplitudeLatitudeCenteredLogPartition μ β x p₀ s (latitudeMeshPoint k a b i) D|}
  have hsub : {D | ∃ q∈Icc a b,
      t*((n+1 : ℕ) : ℝ)+amplitudeLatitudeModulusScale n μ β*
        (2*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+z)*Real.sqrt ((b-a)/(k : ℝ))≤
          |amplitudeLatitudeCenteredLogPartition μ β x p₀ s q D|}⊆A∪⋃ i,B i := by
    rintro D ⟨q,hq,hD⟩
    by_cases hA : D∈A
    · exact Or.inl hA
    right
    by_contra hB
    have hnorm : ‖euclideanBank D‖<Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+z :=
      lt_of_not_ge hA
    obtain ⟨i,hi⟩ := latitudeMeshPoint_covers hk hab hq
    have hiI := latitudeMeshPoint_mem hk hab i
    have hqabs : |q|≤1 := abs_le.mpr ⟨ha.trans hq.1,hq.2.trans hb⟩
    have hiabs : |latitudeMeshPoint k a b i|≤1 := abs_le.mpr ⟨ha.trans hiI.1,hiI.2.trans hb⟩
    have hgrid : |amplitudeLatitudeCenteredLogPartition μ β x p₀ s (latitudeMeshPoint k a b i) D|<
        t*((n+1 : ℕ) : ℝ) := by
      apply lt_of_not_ge
      exact fun h => hB (mem_iUnion.mpr ⟨i,h⟩)
    have hd := amplitudeLatitudeCenteredLogPartition_dist_le hn μ hβ x hx p₀ s hs D hqabs hiabs
    have hm : amplitudeLatitudeModulusScale n μ β*(‖euclideanBank D‖+
        Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ))*Real.sqrt |q-latitudeMeshPoint k a b i|≤
        amplitudeLatitudeModulusScale n μ β*(2*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+z)*
          Real.sqrt ((b-a)/(k : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) (amplitudeLatitudeModulusScale_nonneg n μ β)
      · exact Real.sqrt_le_sqrt hi
      · positivity
      · exact mul_nonneg (amplitudeLatitudeModulusScale_nonneg n μ β) (by positivity)
    have htri := abs_add_le
      (amplitudeLatitudeCenteredLogPartition μ β x p₀ s q D-
        amplitudeLatitudeCenteredLogPartition μ β x p₀ s (latitudeMeshPoint k a b i) D)
      (amplitudeLatitudeCenteredLogPartition μ β x p₀ s (latitudeMeshPoint k a b i) D)
    rw [sub_add_cancel] at htri
    linarith
  have hA := euclideanBank_norm_upper_tail n μ hz
  have hB (i : Fin (k+1)) : bankLaw n μ (B i)≤
      ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1))) := by
    have hi := latitudeMeshPoint_mem hk hab i
    exact amplitudeLatitudeLogPartition_pressure_concentration hn μ hβ ht x hx p₀ s hs
      (abs_le.mpr ⟨ha.trans hi.1,hi.2.trans hb⟩)
  calc
    _ ≤ bankLaw n μ (A∪⋃ i,B i) := measure_mono hsub
    _ ≤ bankLaw n μ A+∑ i,bankLaw n μ (B i) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ ENNReal.ofReal (Real.exp (-z^2/2))+∑ _i : Fin (k+1),
        ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1))) :=
      add_le_add hA (Finset.sum_le_sum fun i _ => hB i)
    _ = _ := by simp

theorem sqrt_bankCoordinate_card_le (n : ℕ) (μ : FiniteMixture) :
    Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)≤
      ((μ.maxDegree+1 : ℕ) : ℝ)^2*((n+1 : ℕ) : ℝ)^μ.maxDegree := by
  have hN : (1 : ℝ)≤((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1≤n+1 by omega)
  have hc : (Fintype.card (BankCoordinate n μ) : ℝ)≤
      ((μ.maxDegree+1 : ℕ) : ℝ)^2*((n+1 : ℕ) : ℝ)^μ.maxDegree := by
    exact_mod_cast bankCoordinate_card_le n μ
  have hP : (1 : ℝ)≤((μ.maxDegree+1 : ℕ) : ℝ) := by exact_mod_cast (show 1≤μ.maxDegree+1 by omega)
  have hp : (1 : ℝ)≤((n+1 : ℕ) : ℝ)^μ.maxDegree := one_le_pow₀ hN
  have hh : (1 : ℝ)≤((μ.maxDegree+1 : ℕ) : ℝ)^2*((n+1 : ℕ) : ℝ)^μ.maxDegree := by
    nlinarith [sq_nonneg (((μ.maxDegree+1 : ℕ) : ℝ)-1)]
  nlinarith [Real.sq_sqrt (show (0 : ℝ)≤Fintype.card (BankCoordinate n μ) by positivity),
    Real.sqrt_nonneg (Fintype.card (BankCoordinate n μ) : ℝ)]

theorem amplitudeLatitude_polynomial_mesh_error_le (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    {a b : ℝ} (ha : -1≤a) (hb : b≤1) (hab : a≤b) :
    amplitudeLatitudeModulusScale n μ β*
      (2*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+Real.sqrt (((n+1 : ℕ) : ℝ)))*
        Real.sqrt ((b-a)/(latitudeMeshSize n μ.maxDegree : ℝ))≤
      8*|β| * Real.sqrt (μ.xi1 1)*(2*((μ.maxDegree+1 : ℕ) : ℝ)^2+1) := by
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let P : ℕ := μ.maxDegree
  have hN : 1≤N := by dsimp [N];exact_mod_cast (show 1≤n+1 by omega)
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hsN : Real.sqrt N≤N := by nlinarith [Real.sq_sqrt hN0.le,Real.sqrt_nonneg N]
  have hpow : N^P≤N^(P+1) := pow_le_pow_right₀ hN (by omega)
  have hpow' : N≤N^(P+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hN (show 1≤P+1 by omega)
  have hcN := sqrt_bankCoordinate_card_le n μ
  have hnorm : 2*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+Real.sqrt N≤
      (2*((P+1 : ℕ) : ℝ)^2+1)*N^(P+1) := by
    change Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)≤((P+1 : ℕ) : ℝ)^2*N^P at hcN
    have hm := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ)≤((P+1 : ℕ) : ℝ)^2 by positivity)
    nlinarith
  have hscale : amplitudeLatitudeModulusScale n μ β≤4*|β| * Real.sqrt (μ.xi1 1)*N := by
    unfold amplitudeLatitudeModulusScale
    exact mul_le_mul_of_nonneg_left hsN (by positivity)
  have herr := latitudeMesh_radius_le n P ha hb hab
  calc
    _ ≤ (4*|β| * Real.sqrt (μ.xi1 1)*N)*
        ((2*((P+1 : ℕ) : ℝ)^2+1)*N^(P+1))*(2/N^(P+2)) := by
      apply mul_le_mul
      · exact mul_le_mul hscale hnorm (by positivity) (by positivity)
      · exact herr
      · positivity
      · positivity
    _ = _ := by
      rw [show P+2=(P+1)+1 by omega,pow_succ]
      field_simp
      simp only [pow_succ]
      ring

/-- Exponential concentration of the literal bank latitude continuum.
The threshold is uniform over reference axes and the entire amplitude box. -/
theorem amplitudeLatitude_uniform_concentration_eventually
    (μ : FiniteMixture) {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) (p₀ : Degree μ.maxDegree) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ (a b : ℝ),-1≤a → b≤1 → a≤b →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        bankLaw n μ {D | ∃ r∈Icc a b,
          ε*((n+1 : ℕ) : ℝ)≤|amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D|}≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  let α : ℝ := (ε/2)^2/(8*β^2*μ.xi 1)
  have hα : 0<α := by
    have hcov := μ.xi_pos (by norm_num : (0 : ℝ)<1)
    dsimp [α]
    positivity
  obtain ⟨γ,hγ,hγtail⟩ := latitude_polynomial_tail_eventually_le (2*(μ.maxDegree+2)) hα
  let K : ℝ := 8*|β| * Real.sqrt (μ.xi1 1)*(2*((μ.maxDegree+1 : ℕ) : ℝ)^2+1)
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hK : ∀ᶠ n : ℕ in atTop,K≤(ε/2)*((n+1 : ℕ) : ℝ) :=
    (hN.const_mul_atTop (by positivity : 0<ε/2)).eventually (eventually_ge_atTop K)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hγtail,hK,eventually_ge_atTop 1] with n htail hK hn
  intro s hs a b ha hb hab x hx
  have hmesh := amplitudeLatitude_uniform_concentration_finite_mesh hn (latitudeMeshSize_pos n μ.maxDegree)
    μ hβ (show 0<ε/2 by positivity) (Real.sqrt_nonneg (((n+1 : ℕ) : ℝ))) ha hb hab x hx p₀ s hs
  have herr := amplitudeLatitude_polynomial_mesh_error_le n μ β ha hb hab
  have hsubset : {D : BankDisorder n μ | ∃ r∈Icc a b,
      ε*((n+1 : ℕ) : ℝ)≤|amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D|}⊆
      {D : BankDisorder n μ | ∃ r∈Icc a b,
        (ε/2)*((n+1 : ℕ) : ℝ)+amplitudeLatitudeModulusScale n μ β*
          (2*Real.sqrt (Fintype.card (BankCoordinate n μ) : ℝ)+Real.sqrt (((n+1 : ℕ) : ℝ)))*
            Real.sqrt ((b-a)/(latitudeMeshSize n μ.maxDegree : ℝ))≤
              |amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D|} := by
    rintro D ⟨r,hr,hD⟩
    refine ⟨r,hr,?_⟩
    change _≤K at herr
    linarith
  have heα : -((ε/2)^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1)=
      -α*((n+1 : ℕ) : ℝ) := by unfold α;ring
  rw [Real.sq_sqrt (by positivity),heα] at hmesh
  apply ((measure_mono hsubset).trans hmesh).trans
  have hrhs : ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)/2))+
      ((latitudeMeshSize n μ.maxDegree+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal (2*Real.exp (-α*((n+1 : ℕ) : ℝ)))=
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)/2)+
        2*((((n+1 : ℕ) : ℝ))^(2*(μ.maxDegree+2))+1)*Real.exp (-α*((n+1 : ℕ) : ℝ))) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [latitudeMeshSize,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
    ring
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal htail

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
