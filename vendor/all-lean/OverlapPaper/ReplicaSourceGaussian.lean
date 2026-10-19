module
public import OverlapPaper.ReplicaSourceDefinitions
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

/-! A literal standard-Gaussian realization of the source disorder. Its
single-replica coefficient norm is the exact covariance diagonal; summing
replicas gives a dimension-uniform Gaussian Lipschitz constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace OverlapPaper
set_option maxHeartbeats 800000

def sourceGaussianRealization (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) : Disorder n →L[ℝ] Disorder n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (finiteCovariance ξ n))

theorem hasLaw_sourceGaussianRealization (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) :
    HasLaw (sourceGaussianRealization ξ n) (disorderLaw ξ n) (stdGaussian (Disorder n)) := by
  convert hasLaw_map (sourceGaussianRealization ξ n).measurable.aemeasurable using 1
  simp only [disorderLaw, multivariateGaussian, zero_add, sourceGaussianRealization]

def sourceGaussianCoordinate (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ)
    (σ : Configuration n) : Disorder n →L[ℝ] ℝ :=
  (EuclideanSpace.proj σ).comp (sourceGaussianRealization ξ n)

theorem sourceGaussianCoordinate_norm_sq (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (n : ℕ) (hn : 0 < n) (σ : Configuration n) :
    ‖sourceGaussianCoordinate ξ n σ‖ ^ 2 = (n : ℝ) * ξ.value 1 := by
  have H := (hasLaw_sourceGaussianRealization ξ n).covariance_fun_comp
    (f := fun g => hamiltonian g σ) (g := fun g => hamiltonian g σ)
    (by unfold hamiltonian; fun_prop) (by unfold hamiltonian; fun_prop)
  rw [covariance_hamiltonian, overlap_self hn] at H
  change cov[sourceGaussianCoordinate ξ n σ, sourceGaussianCoordinate ξ n σ; stdGaussian (Disorder n)] = _ at H
  rw [covariance_self (sourceGaussianCoordinate ξ n σ).continuous.aemeasurable, variance_dual_stdGaussian] at H
  exact H

theorem sourceGaussianCoordinate_norm (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (n : ℕ) (hn : 0 < n) (σ : Configuration n) :
    ‖sourceGaussianCoordinate ξ n σ‖ = Real.sqrt ((n : ℝ) * ξ.value 1) := by
  rw [← sourceGaussianCoordinate_norm_sq ξ n hn σ, Real.sqrt_sq (norm_nonneg _)]

def sourceReplicaGaussianCoefficient {n d : ℕ} (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (σ : ReplicaConfiguration n d) : Disorder n →L[ℝ] ℝ :=
  ∑ l : Fin d, sourceGaussianCoordinate ξ n (σ l)

theorem sourceReplicaGaussianCoefficient_norm_le {n d : ℕ}
    (ξ : FourPapersCommon.AdmissibleEvenMixture) (hn : 0 < n) (σ : ReplicaConfiguration n d) :
    ‖sourceReplicaGaussianCoefficient ξ σ‖ ≤ (d : ℝ) * Real.sqrt ((n : ℝ) * ξ.value 1) := by
  calc
    _ ≤ ∑ l : Fin d, ‖sourceGaussianCoordinate ξ n (σ l)‖ := norm_sum_le _ _
    _ = _ := by simp only [sourceGaussianCoordinate_norm ξ n hn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sourceReplicaGaussianCoefficient_apply {n d : ℕ}
    (ξ : FourPapersCommon.AdmissibleEvenMixture) (σ : ReplicaConfiguration n d) (z : Disorder n) :
    sourceReplicaGaussianCoefficient ξ σ z = ∑ l : Fin d, (sourceGaussianRealization ξ n z) (σ l) := by
  simp only [sourceReplicaGaussianCoefficient, ContinuousLinearMap.sum_apply,
    sourceGaussianCoordinate, ContinuousLinearMap.comp_apply]
  rfl

theorem finite_log_sum_exp_lipschitz {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] [Nonempty I] (A : I → E →L[ℝ] ℝ) (b : I → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    LipschitzWith C.toNNReal (fun x => Real.log (∑ i, Real.exp (A i x + b i))) := by
  let Z : E → ℝ := fun x => ∑ i, Real.exp (A i x + b i)
  have hZpos (x : E) : 0 < Z x :=
    Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
      ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩
  have hlog (x y : E) : Real.log (Z x) ≤ Real.log (Z y) + C * dist x y := by
    have hterm (i : I) : A i x + b i ≤ A i y + b i + C * dist x y := by
      have hop := (A i).le_opNorm (x - y)
      have hnorm : ‖A i (x - y)‖ ≤ C * ‖x - y‖ :=
        hop.trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
      have hle : A i (x - y) ≤ C * ‖x - y‖ :=
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)
      rw [map_sub, ← dist_eq_norm] at hle
      linarith
    have hsum : Z x ≤ Real.exp (C * dist x y) * Z y := by
      dsimp [Z]
      calc
        _ ≤ ∑ i, Real.exp (A i y + b i + C * dist x y) :=
          Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (hterm i)
        _ = _ := by simp_rw [Real.exp_add]; rw [Finset.mul_sum]; congr 1; ext i; ring
    have H := Real.log_le_log (hZpos x) hsum
    rw [Real.log_mul (Real.exp_ne_zero _) (hZpos y).ne', Real.log_exp] at H
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Real.log (Z x)) (Real.log (Z y)) ≤ (C.toNNReal : ℝ) * dist x y
  rw [Real.coe_toNNReal _ hC, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have := hlog y x
    rw [dist_comm] at this
    linarith
  · linarith [hlog x y]

theorem source_covariance_at_one_pos (ξ : FourPapersCommon.AdmissibleEvenMixture) :
    0 < ξ.value 1 := by
  rcases ξ.nonzero with ⟨p, hp⟩
  simpa only [FourPapersCommon.AdmissibleEvenMixture.value, one_pow, mul_one]
    using ξ.summable_coefficient.tsum_pos ξ.nonneg p hp

def sourceGaussianLip (ξ : FourPapersCommon.AdmissibleEvenMixture) (n d : ℕ) : ℝ :=
  (d : ℝ) * Real.sqrt ((n : ℝ) * ξ.value 1) / (n : ℝ)

theorem sourceGaussianLip_pos (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) : 0 < sourceGaussianLip ξ n d := by
  unfold sourceGaussianLip
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  exact div_pos (mul_pos hdr (Real.sqrt_pos.mpr (mul_pos hnr (source_covariance_at_one_pos ξ)))) hnr

theorem continuous_replicaSourcePressureValue {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (hs : (replicaOverlapShell n d D η).Nonempty) :
    Continuous (replicaSourcePressureValue (n := n) h θ J D η) := by
  unfold replicaSourcePressureValue
  apply Continuous.div_const
  apply Continuous.log
  · unfold replicaSourcePartition replicaSourceEnergy totalHamiltonian hamiltonian
    fun_prop
  · exact fun g => (replicaSourcePartition_pos h θ J D η g hs).ne'

theorem replicaSourcePressureGaussian_lipschitz {n d : ℕ}
    (ξ : FourPapersCommon.AdmissibleEvenMixture) (hn : 0 < n)
    (h θ : ℝ) (J : Finset (Fin d)) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (hs : (replicaOverlapShell n d D η).Nonempty) :
    LipschitzWith (sourceGaussianLip ξ n d).toNNReal
      (fun z => replicaSourcePressureValue h θ J D η (sourceGaussianRealization ξ n z)) := by
  classical
  let S := {σ : ReplicaConfiguration n d // σ ∈ replicaOverlapShell n d D η}
  haveI : Nonempty S := by
    rcases hs with ⟨σ,hσ⟩
    exact ⟨⟨σ,hσ⟩⟩
  let A : S → Disorder n →L[ℝ] ℝ := fun σ => sourceReplicaGaussianCoefficient ξ σ.1
  let b : S → ℝ := fun σ => h * (∑ l : Fin d, ∑ i : Fin n, spin (σ.1 l i)) +
    θ * (n : ℝ) * replicaSourceAverage J σ.1
  let C := (d : ℝ) * Real.sqrt ((n : ℝ) * ξ.value 1)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _)
  have H := finite_log_sum_exp_lipschitz A b C hC
    (fun σ => sourceReplicaGaussianCoefficient_norm_le ξ hn σ.1)
  have he (z : Disorder n) : replicaSourcePartition h θ J D η (sourceGaussianRealization ξ n z) =
      ∑ σ : S, Real.exp (A σ z + b σ) := by
    calc
      _ = ∑ σ : S, Real.exp (replicaSourceEnergy h θ J (sourceGaussianRealization ξ n z) σ.1) :=
        (Finset.sum_coe_sort (replicaOverlapShell n d D η)
          (fun σ => Real.exp (replicaSourceEnergy h θ J (sourceGaussianRealization ξ n z) σ))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ hσ
        congr 1
        simp only [A, b, sourceReplicaGaussianCoefficient_apply, replicaSourceEnergy,
          totalHamiltonian, hamiltonian, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have HH := H.dist_le_mul z w
  simp only [Real.coe_toNNReal _ hC, Real.dist_eq] at HH
  rw [Real.coe_toNNReal _ (show 0 ≤ sourceGaussianLip ξ n d from div_nonneg hC hnpos.le)]
  simp only [replicaSourcePressureValue, he, Real.dist_eq, ← sub_div, abs_div,
    abs_of_pos hnpos, sourceGaussianLip]
  apply (div_le_iff₀ hnpos).mpr
  convert HH using 1 <;> dsimp [C] <;> field_simp <;> ring

end OverlapPaper
