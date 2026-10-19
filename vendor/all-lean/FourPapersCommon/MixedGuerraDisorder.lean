module
public import FourPapersCommon.MixedCascadeCalculus
public import FourPapersCommon.GaussianFreeEnergyIBP
public import FourPapersCommon.MixtureConvexity

@[expose] public section

/-! The actual arbitrary even-mixture disorder contraction in Guerra's cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

structure MixedDisorder (N : ℕ) (ξ : AdmissibleEvenMixture) where
  U : Ω → EnergySpace N
  hU : IsGaussianHilbert.{u, 0, 0} U
  covariance : ∀ σ τ, (∫ ω, U ω σ * U ω τ ∂ℙ) = (N : ℝ) * ξ.value (overlap N σ τ)

theorem mixedDisorder_covariance_spectral_sum {N : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) N ξ) (σ τ : Config N) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * (sk.hU.w i σ * sk.hU.w i τ)) =
      (N : ℝ) * ξ.value (overlap N σ τ) := by
  have hh := gaussianLinearImage_secondMoment sk.U sk.hU
    (ContinuousLinearMap.id ℝ (EnergySpace N)) (ContinuousLinearMap.id ℝ (EnergySpace N)) σ τ
  simp only [ContinuousLinearMap.id_apply] at hh
  rw [sk.covariance] at hh
  simpa only [mul_assoc] using hh.symm

theorem mixedGuerra_disorder_hessian {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) N ξ)
    {k : ℕ} (s : RSBScheme k) (U : EnergySpace N)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin N → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * guerraUUD N s β U (sk.hU.w i) (sk.hU.w i) h t j y) =
      (t * N) * (ξ.value 1 -
        guerraMass s j * guerraReplicaAvg N s β U h t j (fun σ τ => ξ.value (overlap N σ τ)) y -
        guerraReplicaAccum N s β U h t (fun _ σ τ => ξ.value (overlap N σ τ)) j y) := by
  have hd : ∀ σ : Config N, overlap N σ σ = 1 := by
    intro σ
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hs : ∀ i, spin N σ i * spin N σ i = 1 := by
      intro i
      have hh := abs_spin N σ i
      nlinarith [sq_abs (spin N σ i)]
    simp [overlap, hs, hNR]
  rw [guerraUUD_trace_replicas N s β U h ht]
  simp_rw [mixedDisorder_covariance_spectral_sum ξ sk, hd]
  rw [guerraMean_const N s β U h ht, guerraReplicaAvg_const_mul, guerraReplicaAccum_const_mul]
  ring

theorem mixedGuerra_disorder_expectation {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) N ξ) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω, guerraUD N s β (sk.U ω) (sk.U ω) h t (k + 2) 0 ∂ℙ) =
      (t * N) * (ξ.value 1 - ∫ ω,
        guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => ξ.value (overlap N σ τ)) (k + 2) 0 ∂ℙ) := by
  have hA := mixed_integrable_guerraReplicaAccum β h sk.U sk.hU s ht (fun _ σ τ => ξ.abs_value_le_at_one (abs_overlap_le_one hN σ τ)) (k + 2) 0
  have hI : ∀ i : sk.hU.ι, Integrable (fun ω => (sk.hU.τ i : ℝ) *
      guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t (k + 2) 0) ℙ := by
    intro i
    apply Integrable.const_mul
    apply integrable_comp_of_affine_norm_bound sk.hU
      ((measurable_guerraUUD_joint s β (sk.hU.w i) (sk.hU.w i) h t (k + 2)).comp
        (f := fun U : EnergySpace N => (U, (0 : Fin N → ℝ))) (measurable_id.prodMk measurable_const))
      (C := guerraUUBound N (sk.hU.w i) (sk.hU.w i) t (k + 2)) (D := 0)
      (guerraUUBound_nonneg _ _ _ _ _) le_rfl
    intro U
    simpa only [Function.comp_apply, zero_mul, add_zero] using
      abs_guerraUUD_le N s β U (sk.hU.w i) (sk.hU.w i) h ht (k + 2) 0
  calc
    _ = ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
        ∫ ω, guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t (k + 2) 0 ∂ℙ :=
      mixed_guerra_disorder_stein β h sk.U sk.hU s ht (k + 2) 0
    _ = ∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
        guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t (k + 2) 0 ∂ℙ := by
      rw [integral_finsetSum _ (fun i _ => hI i)]
      simp only [integral_const_mul]
    _ = ∫ ω, (t * N) * (ξ.value 1 -
        guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => ξ.value (overlap N σ τ)) (k + 2) 0) ∂ℙ := by
      apply integral_congr_ae
      filter_upwards with ω
      simpa only [guerraMass_top, zero_mul, sub_zero] using
        mixedGuerra_disorder_hessian hN β h ξ sk s (sk.U ω) ht (k + 2) 0
    _ = _ := by
      rw [integral_const_mul, integral_sub (integrable_const (ξ.value 1)) hA]
      simp only [integral_const, probReal_univ, one_smul]


end FourPapersCommon
