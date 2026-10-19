-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalParisiSphereNetMaximum

/-! Actual finite Gaussian net pressure controls the original sphere
ground maximum with the proved covering entropy and derivative error. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory Set
open SphericalAging.FiniteModel PureTensorJetBounds FiniteTensorMixtureMaximum SphericalParisiGroundRSUpper
open SphericalParisiGaussianREMJensen
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {N k : ℕ}

theorem logAverageExp_abs_le (hk : 0 < k) (f : Fin k → ℝ) {M : ℝ}
    (hf : ∀ j,|f j| ≤ M) : |logAverageExp k f| ≤ M := by
  unfold logAverageExp
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlo : Real.exp (-M) ≤ (∑ j,Real.exp (f j)) / (k : ℝ) := by
    apply (le_div_iff₀ hkr).mpr
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Real.exp_le_exp.mpr (abs_le.mp (hf j)).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using h
  have hhi : (∑ j,Real.exp (f j)) / (k : ℝ) ≤ Real.exp M := by
    apply (div_le_iff₀ hkr).mpr
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Real.exp_le_exp.mpr (abs_le.mp (hf j)).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using h
  apply abs_le.mpr
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-M)) hlo
  · simpa only [Real.log_exp] using Real.log_le_log ((Real.exp_pos (-M)).trans_le hlo) hhi

def netLogAverage (d : σ → ℕ) (c : σ → ℝ) (points : Fin k → UnitSphere N) (β : ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : ℝ :=
  logAverageExp k (fun j => β * inner ℝ (feature d c (points j).val) g)

omit [DecidableEq σ] in
theorem netLogAverage_integrable (hk : 0 < k) (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) (β : ℝ) :
    Integrable (netLogAverage d c points β)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) := by
  let C := |β| * ∑ j,‖feature d c (points j).val‖
  have hm : Measurable (netLogAverage d c points β) := by
    unfold netLogAverage logAverageExp
    fun_prop
  apply (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul C).mono' hm.aestronglyMeasurable
  exact .of_forall fun g => by
    rw [Real.norm_eq_abs]
    apply logAverageExp_abs_le hk
    intro j
    rw [abs_mul]
    have hpoint := abs_real_inner_le_norm (feature d c (points j).val) g
    have hsum : ‖feature d c (points j).val‖ ≤ ∑ l,‖feature d c (points l).val‖ :=
      Finset.single_le_sum (f := fun l : Fin k => ‖feature d c (points l).val‖)
        (fun l _ => norm_nonneg _) (Finset.mem_univ j)
    calc
      _ ≤ |β| * (‖feature d c (points j).val‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left hpoint (abs_nonneg β)
      _ ≤ |β| * ((∑ l,‖feature d c (points l).val‖) * ‖g‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsum (norm_nonneg g)) (abs_nonneg β)
      _ = _ := by dsimp [C];ring

omit [DecidableEq σ] in
theorem netMaximum_le_netLogAverage (hk : 0 < k) (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) {β : ℝ} (hβ : 0 < β)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    netMaximum d c points g ≤ netLogAverage d c points β g / β + Real.log (k : ℝ) / β := by
  let : NeZero k := ⟨hk.ne'⟩
  apply ciSup_le
  intro j
  let S : ℝ := ∑ l,Real.exp (β * inner ℝ (feature d c (points l).val) g)
  have hj : Real.exp (β * inner ℝ (feature d c (points j).val) g) ≤ S :=
    Finset.single_le_sum
      (f := fun l : Fin k => Real.exp (β * inner ℝ (feature d c (points l).val) g))
      (fun l _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  have hS : 0 < S := (Real.exp_pos _).trans_le hj
  have h := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp] at h
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have he : netLogAverage d c points β g = Real.log S - Real.log (k : ℝ) := by
    exact Real.log_div hS.ne' hkr.ne'
  rw [he]
  rw [← add_div,sub_add_cancel]
  exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using h)

theorem expected_netMaximum_le_netLogAverage (hk : 0 < k) (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) {β : ℝ} (hβ : 0 < β) :
    (∫ g,netMaximum d c points g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
      (∫ g,netLogAverage d c points β g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) / β +
        Real.log (k : ℝ) / β := by
  have hi := (netLogAverage_integrable hk d c points β).div_const β
  have h := integral_mono (netMaximum_integrable hk d c points) (hi.add (integrable_const _))
    (netMaximum_le_netLogAverage hk d c points hβ)
  simp only [Pi.add_apply] at h
  simpa only [integral_add hi (integrable_const _),integral_div,integral_const,probReal_univ,one_smul] using h

omit [DecidableEq σ] in
theorem netLogAverage_le_beta_netMaximum (hk : 0 < k) (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) {β : ℝ} (hβ : 0 < β)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    netLogAverage d c points β g ≤ β*netMaximum d c points g := by
  let : NeZero k := ⟨hk.ne'⟩
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsum : (∑ j,Real.exp (β*inner ℝ (feature d c (points j).val) g))/(k : ℝ) ≤
      Real.exp (β*netMaximum d c points g) := by
    apply (div_le_iff₀ hkr).mpr
    have H := Finset.sum_le_sum (s := Finset.univ) (fun j _ => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left
        (le_ciSup (Set.finite_range (fun l : Fin k => inner ℝ (feature d c (points l).val) g)).bddAbove j) hβ.le))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm,netMaximum] using H
  have hpos : 0 < (∑ j,Real.exp (β*inner ℝ (feature d c (points j).val) g))/(k : ℝ) := by
    apply div_pos _ hkr
    exact (Real.exp_pos (β*inner ℝ (feature d c (points ⟨0,hk⟩).val) g)).trans_le
      (Finset.single_le_sum
        (f := fun j : Fin k => Real.exp (β*inner ℝ (feature d c (points j).val) g))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ (⟨0,hk⟩ : Fin k)))
  simpa only [netLogAverage,logAverageExp,Real.log_exp] using Real.log_le_log hpos hsum

/-- Exact normalized Gaussian finite-net maximum/pressure error, bounded
by its literal finite entropy. Both integrability and inequalities are proved. -/
theorem expected_net_pressure_maximum_error (hN : 0 < N) (hk : 0 < k)
    (d : σ → ℕ) (c : σ → ℝ) (points : Fin k → UnitSphere N)
    {β : ℝ} (hβ : 0 < β) :
    0 ≤ (∫ g,netMaximum d c points g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ)-
        (∫ g,netLogAverage d c points β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(β*(N : ℝ)) ∧
    (∫ g,netMaximum d c points g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ)-
        (∫ g,netLogAverage d c points β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(β*(N : ℝ)) ≤
      Real.log (k : ℝ)/(β*(N : ℝ)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have H := integral_mono (netLogAverage_integrable hk d c points β)
    ((netMaximum_integrable hk d c points).const_mul β)
    (netLogAverage_le_beta_netMaximum hk d c points hβ)
  rw [integral_const_mul] at H
  have HL := div_le_div_of_nonneg_right
    ((div_le_iff₀ hβ).mpr (by simpa only [mul_comm] using H)) hNr.le
  rw [div_div] at HL
  have HU := div_le_div_of_nonneg_right
    (expected_netMaximum_le_netLogAverage hk d c points hβ) hNr.le
  rw [add_div,div_div,div_div] at HU
  exact ⟨sub_nonneg.mpr HL,by linarith⟩

/-- The original Gaussian sphere maximum is controlled by an actual
finite Gaussian pressure, with genuine Euclidean entropy and O(ε N) error. -/
theorem exists_actual_net_ground_pressure_bound (hN : 0 < N) (d : σ → ℕ) (c : σ → ℝ)
    (hd : ∀ i,1 ≤ d i) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ (k : ℕ) (points : Fin k → UnitSphere N),0 < k ∧
      (∀ x : UnitSphere N,∃ j,‖x.val - (points j).val‖ ≤ ε) ∧
      Real.log (k : ℝ) ≤ (N : ℝ) * Real.log (1 + 2 / ε) ∧
      (∫ g,actualMaximum (N := N) d c g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
        (∫ g,netLogAverage d c points β g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) / β +
          (N : ℝ) * Real.log (1 + 2 / ε) / β + derivativeConstant d c * ε * (N : ℝ) := by
  obtain ⟨k,points,hk,hcover,hcard,hmax⟩ := exists_actual_unitSphere_net_expected_maximum hN d c hd hε
  refine ⟨k,points,hk,hcover,hcard,?_⟩
  exact hmax.trans (add_le_add
    ((expected_netMaximum_le_netLogAverage hk d c points hβ).trans
      (add_le_add le_rfl (div_le_div_of_nonneg_right hcard hβ.le))) le_rfl)

end SlowEquilibration.SphericalParisiSphereNet
