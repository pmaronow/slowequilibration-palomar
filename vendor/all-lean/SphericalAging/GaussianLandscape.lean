module

public import SphericalAging.EuclideanNets
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Probability.Moments.SubGaussian

public section

/-!
# The actual ordered Gaussian landscape norm

The multilinear form is constructed from the same nonsymmetrized tensor
couplings as FiniteModel. The unit-sphere net reduction below applies to its
actual continuous multilinear operator norm.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace SphericalAging.GaussianLandscape
open FiniteModel EuclideanNets

@[expose] abbrev TensorForm (N p : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin p => Vector N) ℝ

@[expose] def coordinateForm (N p : ℕ) (I : TensorIndex N p) : TensorForm N p :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin p) ℝ).compContinuousLinearMap
    (fun k => PiLp.proj 2 (fun _ : Fin N => ℝ) (I k))

@[expose] def tensorForm (N p : ℕ) (J : Disorder N p) : TensorForm N p :=
  ∑ I : TensorIndex N p, J I • coordinateForm N p I

theorem tensorForm_apply (N p : ℕ) (J : Disorder N p) (v : Fin p → Vector N) :
    tensorForm N p J v=∑ I : TensorIndex N p, J I*(∏ k : Fin p, v k (I k)) := by
  classical
  simp [tensorForm,coordinateForm,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

@[expose] def landscapeNorm (N p : ℕ) (J : Disorder N p) : ℝ := ‖tensorForm N p J‖/Real.sqrt N

theorem tensorForm_continuous (N p : ℕ) : Continuous (tensorForm N p) := by
  classical
  unfold tensorForm
  apply continuous_finsetSum
  intro I _
  exact (continuous_apply I).smul continuous_const

theorem landscapeNorm_continuous (N p : ℕ) : Continuous (landscapeNorm N p) :=
  (tensorForm_continuous N p).norm.div_const _

theorem landscapeNorm_nonnegative (N p : ℕ) (J : Disorder N p) : 0 ≤ landscapeNorm N p J :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Bounding a real multilinear form on products of unit spheres bounds its
operator norm, by actual normalization of every nonzero coordinate. -/
theorem multilinear_norm_le_of_unit_bound {N p : ℕ} (f : TensorForm N p) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ v : Fin p → Vector N, (∀ k, ‖v k‖=1) → ‖f v‖ ≤ B) : ‖f‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro m
  by_cases hz : ∃ k, m k=0
  · obtain ⟨k,hk⟩ := hz
    rw [f.map_coord_zero k hk,norm_zero]
    exact mul_nonneg hB (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  · have hne (k : Fin p) : m k ≠ 0 := by intro hk; exact hz ⟨k,hk⟩
    let v : Fin p → Vector N := fun k => ‖m k‖⁻¹ • m k
    have hv (k : Fin p) : ‖v k‖=1 := by
      dsimp only [v]
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne k))]
    have hm : (fun k => ‖m k‖ • v k)=m := by
      funext k
      dsimp only [v]
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne k)),one_smul]
    have heq := f.map_smul_univ (fun k => ‖m k‖) v
    rw [hm] at heq
    rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (hb v hv) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans_eq
      (mul_comm _ _)

theorem multilinear_norm_net_bound {N p : ℕ} (f : TensorForm N p) {ε B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (S : Finset (Vector N))
    (hunit : ∀ x ∈ S, ‖x‖=1)
    (hnet : ∀ x : Vector N, ‖x‖=1 → ∃ y ∈ S, dist x y ≤ ε)
    (hb : ∀ v : Fin p → Vector N, (∀ k, v k ∈ S) → ‖f v‖ ≤ B) :
    ‖f‖ ≤ B+‖f‖*(p : ℝ)*ε := by
  apply multilinear_norm_le_of_unit_bound f (add_nonneg hB (by positivity))
  intro v hv
  choose w hw hdist using (fun k => hnet (v k) (hv k))
  have hvNorm : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun k => (hv k).le)
  have hwNorm : ‖w‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun k => (hunit (w k) (hw k)).le)
  have hdiff : ‖v-w‖ ≤ ε := (pi_norm_le_iff_of_nonneg hε).mpr (fun k => by
    simpa only [Pi.sub_apply,dist_eq_norm] using hdist k)
  have hh := f.norm_image_sub_le v w
  have h1 : max ‖v‖ ‖w‖ ^ (p-1) ≤ 1 := by
    exact pow_le_one₀ (le_trans (norm_nonneg _) (le_max_left _ _)) (max_le hvNorm hwNorm)
  have herror : ‖f v-f w‖ ≤ ‖f‖*(p : ℝ)*ε := hh.trans (by
    simp only [Fintype.card_fin]
    calc
      ‖f‖*p*max ‖v‖ ‖w‖^(p-1)*‖v-w‖ ≤ ‖f‖*p*1*ε := by gcongr
      _ = _ := by ring)
  calc
    ‖f v‖ ≤ ‖f v-f w‖+‖f w‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖f‖*p*ε+B := add_le_add herror (hb w hw)
    _ = B+‖f‖*p*ε := add_comm _ _

/-- The precise factor-two net reduction used for the manuscript's Q_N. -/
theorem multilinear_norm_le_twice_net {N p : ℕ} (hp : 0 < p) (f : TensorForm N p) {B : ℝ}
    (hB : 0 ≤ B) (S : Finset (Vector N))
    (hunit : ∀ x ∈ S, ‖x‖=1)
    (hnet : ∀ x : Vector N, ‖x‖=1 → ∃ y ∈ S, dist x y ≤ 1/(2*(p : ℝ)))
    (hb : ∀ v : Fin p → Vector N, (∀ k, v k ∈ S) → ‖f v‖ ≤ B) : ‖f‖ ≤ 2*B := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh := multilinear_norm_net_bound f (ε := 1/(2*(p : ℝ))) (by positivity) hB S hunit hnet hb
  have heq : ‖f‖*(p : ℝ)*(1/(2*(p : ℝ)))=‖f‖/2 := by field_simp
  rw [heq] at hh
  linarith



@[expose] def directionWeights {N p : ℕ} (v : Fin p → Vector N) (I : TensorIndex N p) : ℝ :=
  ∏ k : Fin p, v k (I k)

theorem directionWeights_sq_sum {N p : ℕ} (v : Fin p → Vector N) :
    ∑ I : TensorIndex N p, directionWeights v I*directionWeights v I=
      ∏ k : Fin p, ‖v k‖^2 := by
  classical
  simp only [directionWeights,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k : Fin p => fun i : Fin N => v k i*v k i)]
  apply Finset.prod_congr rfl
  intro k _
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs,sq_abs,pow_two]

theorem tensorForm_eq_tensorLinear (N p : ℕ) (v : Fin p → Vector N) :
    (fun J : Disorder N p => tensorForm N p J v)=tensorLinear (directionWeights v) := by
  funext J
  rw [tensorForm_apply]
  simp only [tensorLinear,directionWeights,mul_comm]

theorem direction_has_standardGaussianLaw {N p : ℕ} (v : Fin p → Vector N)
    (hv : ∀ k, ‖v k‖=1) :
    HasLaw (fun J : Disorder N p => tensorForm N p J v) (gaussianReal 0 1) (disorderLaw N p) := by
  rw [tensorForm_eq_tensorLinear]
  have hG := tensorLinear_hasGaussianLaw (directionWeights v)
  have hvar : variance (tensorLinear (directionWeights v)) (disorderLaw N p)=1 := by
    rw [variance_eq_integral hG.aemeasurable,tensorLinear_mean]
    simp only [sub_zero,pow_two]
    rw [tensorLinear_covariance,directionWeights_sq_sum]
    simp only [hv,one_pow,Finset.prod_const_one]
  refine ⟨hG.aemeasurable,?_⟩
  rw [hG.map_eq_gaussianReal,tensorLinear_mean,hvar,Real.toNNReal_one]

theorem direction_subgaussian {N p : ℕ} (v : Fin p → Vector N)
    (hv : ∀ k, ‖v k‖=1) :
    HasSubgaussianMGF (fun J : Disorder N p => tensorForm N p J v) 1 (disorderLaw N p) := by
  have hLaw := direction_has_standardGaussianLaw v hv
  constructor
  · intro t
    have hi := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t
    rw [← hLaw.map_eq] at hi
    exact hi.comp_aemeasurable hLaw.aemeasurable
  · intro t
    rw [mgf_gaussianReal hLaw]
    simp only [zero_mul,zero_add,NNReal.coe_one,one_mul,le_refl]

/-- Fixed unit-direction contractions of the actual tensor have the standard
Gaussian two-sided tail, without any independence assumption between directions. -/
theorem direction_abs_tail {N p : ℕ} (v : Fin p → Vector N)
    (hv : ∀ k, ‖v k‖=1) {a : ℝ} (ha : 0 ≤ a) :
    (disorderLaw N p).real {J | a < |tensorForm N p J v|} ≤ 2*Real.exp (-a^2/2) := by
  have hsub := direction_subgaussian v hv
  have hpos := hsub.measure_ge_le ha
  have hneg := hsub.neg.measure_ge_le ha
  have hsubset : {J : Disorder N p | a < |tensorForm N p J v|} ⊆
      {J | a ≤ tensorForm N p J v} ∪ {J | a ≤ -tensorForm N p J v} := by
    intro J hJ
    change a < |tensorForm N p J v| at hJ
    rcases lt_abs.mp hJ with hh|hh
    · exact Or.inl hh.le
    · exact Or.inr hh.le
  have hm := (measureReal_mono (μ := disorderLaw N p) hsubset).trans (measureReal_union_le _ _)
  have hbounds := add_le_add hpos hneg
  simp only [Pi.neg_apply,NNReal.coe_one,mul_one] at hbounds
  exact hm.trans (by simpa only [two_mul] using hbounds)



theorem tensor_norm_net_tail {N p : ℕ} (hp : 0 < p) (S : Finset (Vector N))
    (hunit : ∀ x ∈ S, ‖x‖=1)
    (hnet : ∀ x : Vector N, ‖x‖=1 → ∃ y ∈ S, dist x y ≤ 1/(2*(p : ℝ)))
    {a : ℝ} (ha : 0 ≤ a) :
    (disorderLaw N p).real {J | a < ‖tensorForm N p J‖} ≤
      2*(S.card : ℝ)^p*Real.exp (-a^2/8) := by
  classical
  let E : (Fin p → S) → Set (Disorder N p) := fun w =>
    {J | a/2 < ‖tensorForm N p J (fun k => (w k : Vector N))‖}
  have hsubset : {J : Disorder N p | a < ‖tensorForm N p J‖} ⊆ ⋃ w : Fin p → S, E w := by
    intro J hJ
    change a < ‖tensorForm N p J‖ at hJ
    by_contra hNo
    have hval (v : Fin p → Vector N) (hv : ∀ k, v k ∈ S) : ‖tensorForm N p J v‖ ≤ a/2 := by
      let w : Fin p → S := fun k => ⟨v k,hv k⟩
      by_contra hbad
      apply hNo
      exact mem_iUnion.mpr ⟨w,lt_of_not_ge hbad⟩
    have hh := multilinear_norm_le_twice_net hp (tensorForm N p J) (B := a/2)
      (by positivity) S hunit hnet hval
    linarith
  have hi := measureReal_iUnion_fintype_le (μ := disorderLaw N p) E
  have hb (w : Fin p → S) : (disorderLaw N p).real (E w) ≤ 2*Real.exp (-a^2/8) := by
    have hh := direction_abs_tail (fun k => (w k : Vector N))
      (fun k => hunit (w k) (w k).property) (a := a/2) (by positivity)
    have heq : -(a/2)^2/2 = -a^2/8 := by ring
    simpa only [E,Real.norm_eq_abs,heq] using hh
  calc
    _ ≤ (disorderLaw N p).real (⋃ w : Fin p → S, E w) := measureReal_mono hsubset
    _ ≤ ∑ w : Fin p → S, (disorderLaw N p).real (E w) := hi
    _ ≤ ∑ _w : Fin p → S, 2*Real.exp (-a^2/8) := Finset.sum_le_sum (fun w _ => hb w)
    _ = 2*(S.card : ℝ)^p*Real.exp (-a^2/8) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_pow]
      ring

/-- The actual Gaussian landscape norm has a dimension-exponential net tail. -/
theorem landscape_tail_net {N p : ℕ} (hN : 0 < N) (hp : 0 < p) {x : ℝ} (hx : 0 ≤ x) :
    (disorderLaw N p).real {J | x < landscapeNorm N p J} ≤
      2*(1+4*(p : ℝ))^(N*p)*Real.exp (-(N : ℝ)*x^2/8) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨S,hunit,hnet,hcard⟩ := unit_sphere_net N (ε := 1/(2*(p : ℝ))) (by positivity)
  have hcard' : (S.card : ℝ) ≤ (1+4*(p : ℝ))^N := by
    have heq : 1+2/(1/(2*(p : ℝ)))=1+4*(p : ℝ) := by field_simp; ring
    simpa only [heq] using hcard
  have hsq := Real.sq_sqrt hNR.le
  have htail := tensor_norm_net_tail hp S hunit hnet (a := x*Real.sqrt N) (by positivity)
  have hset : {J : Disorder N p | x < landscapeNorm N p J}=
      {J : Disorder N p | x*Real.sqrt N < ‖tensorForm N p J‖} := by
    ext J
    exact lt_div_iff₀ (Real.sqrt_pos.mpr hNR)
  have hexp : -(x*Real.sqrt N)^2/8=-(N : ℝ)*x^2/8 := by nlinarith [hsq]
  rw [hset]
  calc
    _ ≤ 2*(S.card : ℝ)^p*Real.exp (-(N : ℝ)*x^2/8) := by simpa only [hexp] using htail
    _ ≤ 2*((1+4*(p : ℝ))^N)^p*Real.exp (-(N : ℝ)*x^2/8) := by gcongr
    _ = _ := by rw [← pow_mul]



@[expose] def entropyConstant (p : ℕ) : ℝ := (p : ℝ)*Real.log (1+4*(p : ℝ))
@[expose] def landscapeThreshold (p : ℕ) : ℝ := 4*(entropyConstant p+1)

theorem entropyConstant_nonnegative (p : ℕ) : 0 ≤ entropyConstant p :=
  mul_nonneg (Nat.cast_nonneg p) (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]))

theorem landscapeThreshold_pos (p : ℕ) : 0 < landscapeThreshold p := by
  unfold landscapeThreshold
  linarith [entropyConstant_nonnegative p]

theorem landscapeThreshold_sq_bound (p : ℕ) {x : ℝ} (hx : landscapeThreshold p ≤ x) :
    16*entropyConstant p ≤ x^2 := by
  have hc := entropyConstant_nonnegative p
  unfold landscapeThreshold at hx
  have hh : 0 ≤ x-4*(entropyConstant p+1) := by linarith
  nlinarith [sq_nonneg (entropyConstant p),mul_nonneg hh (show 0 ≤ x+4*(entropyConstant p+1) by linarith)]

/-- The manuscript's dimension-dependent Gaussian tail past a fixed threshold. -/
theorem landscape_tail_dimension {N p : ℕ} (hN : 0 < N) (hp : 0 < p) {x : ℝ}
    (hx : landscapeThreshold p ≤ x) :
    (disorderLaw N p).real {J | x < landscapeNorm N p J} ≤
      2*Real.exp (-(N : ℝ)*x^2/16) := by
  have hx0 := (landscapeThreshold_pos p).le.trans hx
  have hh := landscape_tail_net hN hp hx0
  have hbase : 0 < 1+4*(p : ℝ) := by positivity
  have hpow : (1+4*(p : ℝ))^(N*p)=Real.exp ((N : ℝ)*entropyConstant p) := by
    rw [← Real.exp_log hbase,← Real.exp_nat_mul]
    congr 1
    unfold entropyConstant
    push_cast
    ring
  rw [hpow] at hh
  have heq : 2*Real.exp ((N : ℝ)*entropyConstant p)*Real.exp (-(N : ℝ)*x^2/8)=
      2*Real.exp ((N : ℝ)*entropyConstant p-(N : ℝ)*x^2/8) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [heq] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hb := mul_le_mul_of_nonneg_left (landscapeThreshold_sq_bound p hx) (Nat.cast_nonneg N)
  nlinarith

/-- A single Gaussian tail bound valid uniformly in every dimension N≥2. -/
theorem landscape_tail_uniform {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) {x : ℝ}
    (hx : landscapeThreshold p ≤ x) :
    (disorderLaw N p).real {J | x < landscapeNorm N p J} ≤ 2*Real.exp (-x^2/8) := by
  have hN0 : 0 < N := by omega
  have hh := landscape_tail_dimension hN0 hp hx
  refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [mul_nonneg (sub_nonneg.mpr hNR) (sq_nonneg x)]

/-- The probability of exceeding a p-dependent constant decays exponentially
in N, for the actual ordered Gaussian disorder law. -/
theorem landscape_exponential_dimension_bound {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) :
    (disorderLaw N p).real {J | landscapeThreshold p+4 < landscapeNorm N p J} ≤
      Real.exp (-(N : ℝ)) := by
  have hN0 : 0 < N := by omega
  have hh := landscape_tail_dimension hN0 hp (x := landscapeThreshold p+4) (by linarith)
  have hA : 4 ≤ landscapeThreshold p := by unfold landscapeThreshold; linarith [entropyConstant_nonnegative p]
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : 64 ≤ (landscapeThreshold p+4)^2 := by nlinarith
  have hexp : 2*Real.exp (-(N : ℝ)*(landscapeThreshold p+4)^2/16) ≤
      2*Real.exp (-4*(N : ℝ)) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    nlinarith [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hsq)]
  have h2 : 2 ≤ Real.exp (3*(N : ℝ)) :=
    (show 2 ≤ 1+3*(N : ℝ) by linarith).trans (by simpa only [add_comm] using Real.add_one_le_exp (3*(N : ℝ)))
  calc
    _ ≤ 2*Real.exp (-4*(N : ℝ)) := hh.trans hexp
    _ ≤ Real.exp (3*(N : ℝ))*Real.exp (-4*(N : ℝ)) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = Real.exp (-(N : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

end SphericalAging.GaussianLandscape
