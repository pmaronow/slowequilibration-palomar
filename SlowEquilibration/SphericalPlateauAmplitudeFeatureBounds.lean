-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeLatitudeFeature
public import SlowEquilibration.FiniteNonnegativePolynomialTangent
public import SlowEquilibration.SphericalLatitudeRegularity

@[expose] public section

/-! # Primitive physical bounds for the actual amplitude bank

Coordinate rescaling controls the literal amplitude feature by twice its
original feature. Canonical Parseval identifies the original Gram, giving
the true covariance norm and spatial increment bounds. The latitude chord
estimate and actual tensor cardinalities then give the mesh inputs.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set SphericalModel GaussianSpinComparison
open scoped Topology BigOperators RealInnerProductSpace
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem bankAmplitude_abs_le_two (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) (i : BankIndex μ) :
    |bankAmplitude p₀ s i|≤2 := by
  unfold bankAmplitude
  split_ifs
  · exact hs 0
  · exact hs 1
  · norm_num

theorem amplitudeBankFeature_eq_diagonal (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) :
    amplitudeBankFeature μ x e p₀ s u=
      diagonal (fun j : BankCoordinate n μ => bankAmplitude p₀ s j.1)
        (amplitudeBankFeature μ x e p₀ (fun _ => 1) u) := by
  ext j
  simp only [diagonal_apply,amplitudeBankFeature,bankAmplitude_one,one_mul]
  ring

/-- The actual canonical original bank Gram is the original covariance. -/
theorem amplitudeBankFeature_inner_one_canonical (μ : FiniteMixture) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree) (u v : Vector (n+1)) :
    inner ℝ (amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) u)
      (amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) v)=
        ((n+1 : ℕ) : ℝ)*μ.xi (overlap u v) := by
  rw [amplitudeBankFeature_inner,← amplitudeField_covariance]
  simpa only [Nat.cast_add,Nat.cast_one] using amplitudeField_covariance_one_of_parseval μ x (latitudeFrameAt x)
    (by intro u v;simpa only [Nat.cast_add,Nat.cast_one] using latitudeFrameAt_adjoint_inner x hx u v) p₀ u v

/-- Exact identification of the source polynomial derivative at one. -/
theorem spatialVariance_mixture_eq_xi1 (μ : FiniteMixture) :
    spatialVariance (mixtureCoefficients μ)=μ.xi1 1 := by
  have h := FiniteNonnegativePolynomial.covariance_hasDerivAt
    (fun p : Degree μ.maxDegree => p.val.val) (mixtureCoefficients μ) (1 : ℝ)
  have he : FiniteNonnegativePolynomial.covariance (fun p : Degree μ.maxDegree => p.val.val)
      (mixtureCoefficients μ)=μ.xi := funext (covariancePolynomial_mixture μ)
  rw [he] at h
  have hh := h.unique (μ.hasDerivAt_xi 1)
  simpa only [FiniteNonnegativePolynomial.firstDerivative,one_pow,mul_one,spatialVariance] using hh

theorem amplitudeBankFeature_norm_one_canonical (μ : FiniteMixture) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
    ‖amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) u‖=
      Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1) := by
  have hh := amplitudeBankFeature_inner_one_canonical μ x hx p₀ u u
  rw [real_inner_self_eq_norm_sq,overlap_self (by omega) u hu] at hh
  rw [← hh,Real.sqrt_sq (norm_nonneg _)]

/-- True dimension-scaled physical feature norm, uniformly on the entire
source amplitude box before every Gaussian realization. -/
theorem amplitudeBankFeature_norm_le (μ : FiniteMixture) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
    ‖amplitudeBankFeature μ x (latitudeFrameAt x) p₀ s u‖≤
      2*Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1) := by
  rw [amplitudeBankFeature_eq_diagonal]
  have hh := diagonal_norm_le (fun j : BankCoordinate n μ => bankAmplitude p₀ s j.1)
    (by norm_num : (0 : ℝ)≤2) (fun j => bankAmplitude_abs_le_two μ p₀ s hs j.1)
    (amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) u)
  rwa [amplitudeBankFeature_norm_one_canonical μ x hx p₀ u hu] at hh

/-- The original bank increment equals the genuine original tensor feature
increment; this is proved from both literal Gram identities. -/
theorem amplitudeBankFeature_dist_one_eq (μ : FiniteMixture) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree) (u v : Vector (n+1)) :
    ‖amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) u-
      amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) v‖=
        ‖fieldFeature (mixtureCoefficients μ) u-fieldFeature (mixtureCoefficients μ) v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real,norm_sub_sq_real]
  simp only [← real_inner_self_eq_norm_sq]
  rw [amplitudeBankFeature_inner_one_canonical μ x hx p₀ u u,
    amplitudeBankFeature_inner_one_canonical μ x hx p₀ v v,
    amplitudeBankFeature_inner_one_canonical μ x hx p₀ u v]
  simp only [fieldFeature_inner_gram (by omega : 1≤n+1) (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ),covariancePolynomial_mixture]

/-- True spatial increment bound, uniform over both selected amplitudes. -/
theorem amplitudeBankFeature_dist_le (μ : FiniteMixture) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) (u v : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (hv : ‖v‖^2=((n+1 : ℕ) : ℝ)) :
    ‖amplitudeBankFeature μ x (latitudeFrameAt x) p₀ s u-
      amplitudeBankFeature μ x (latitudeFrameAt x) p₀ s v‖≤
        2*Real.sqrt (μ.xi1 1)*‖u-v‖ := by
  rw [amplitudeBankFeature_eq_diagonal μ x (latitudeFrameAt x) p₀ s u,
    amplitudeBankFeature_eq_diagonal μ x (latitudeFrameAt x) p₀ s v,← map_sub]
  have hh := diagonal_norm_le (fun j : BankCoordinate n μ => bankAmplitude p₀ s j.1)
    (by norm_num : (0 : ℝ)≤2) (fun j => bankAmplitude_abs_le_two μ p₀ s hs j.1)
    (amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) u-
      amplitudeBankFeature μ x (latitudeFrameAt x) p₀ (fun _ => 1) v)
  rw [amplitudeBankFeature_dist_one_eq μ x hx p₀ u v] at hh
  have hf := fieldFeature_dist_le (by omega : 1≤n+1) (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) u v hu hv
  rw [spatialVariance_mixture_eq_xi1] at hf
  exact hh.trans (by nlinarith)

/-- Actual global half-Hölder latitude feature bound, including both poles. -/
theorem amplitudeLatitudeBankFeature_dist_le (hn : 1≤n) (μ : FiniteMixture)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1)
    (u : Vector n) (hu : ‖u‖^2=(n : ℝ)) :
    ‖amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s r u-
      amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s q u‖≤
        4*Real.sqrt (μ.xi1 1)*Real.sqrt (((n+1 : ℕ) : ℝ))*Real.sqrt |r-q| := by
  have he := latitudeFrameAt_orthogonal x hx
  have hb := amplitudeBankFeature_dist_le μ x hx p₀ s hs
    (latitudeMap x (latitudeFrameAt x) r u) (latitudeMap x (latitudeFrameAt x) q u)
    (latitudeMap_norm_sq hn x hx (latitudeFrameAt x) he hr u hu)
    (latitudeMap_norm_sq hn x hx (latitudeFrameAt x) he hq u hu)
  have hd := mul_le_mul_of_nonneg_left (latitudeMap_dist_le hn x hx (latitudeFrameAt x) he hr hq u hu)
    (by positivity : 0≤2*Real.sqrt (μ.xi1 1))
  exact (hb.trans hd).trans_eq (by ring)

theorem bankIndex_card_le (μ : FiniteMixture) :
    Fintype.card (BankIndex μ)≤(μ.maxDegree+1)^2 := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _p : Degree μ.maxDegree,(μ.maxDegree+1) := by
      apply Finset.sum_le_sum
      intro p _
      simp only [Fintype.card_fin]
      have hp := p.val.isLt
      omega
    _ = Fintype.card (Degree μ.maxDegree)*(μ.maxDegree+1) := by simp
    _ ≤ _ := by
      have hc : Fintype.card (Degree μ.maxDegree)≤μ.maxDegree+1 := by
        simpa using Fintype.card_subtype_le (fun p : Fin (μ.maxDegree+1) => 2≤p.val)
      simpa only [pow_two] using Nat.mul_le_mul_right (μ.maxDegree+1) hc

/-- Genuine Gaussian coordinate count, polynomial before every dimension. -/
theorem bankCoordinate_card_le (n : ℕ) (μ : FiniteMixture) :
    Fintype.card (BankCoordinate n μ)≤(μ.maxDegree+1)^2*(n+1)^μ.maxDegree := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : BankIndex μ,(n+1)^μ.maxDegree := by
      apply Finset.sum_le_sum
      intro i _
      simp only [SphericalAging.FiniteModel.TensorIndex,Fintype.card_fun,Fintype.card_fin]
      apply (Nat.pow_le_pow_left (Nat.le_succ n) i.2.val).trans
      apply Nat.pow_le_pow_right (by omega : 1≤n+1)
      have hk := i.2.isLt
      have hp := i.1.val.isLt
      omega
    _ = Fintype.card (BankIndex μ)*(n+1)^μ.maxDegree := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (bankIndex_card_le μ)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
