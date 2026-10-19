-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics

@[expose] public section

/-! # Arbitrarily small actual spherical pole mass at an exponential rate -/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def poleRegion {N : ℕ} (x : Vector N) (ρ : ℝ) : Set (Vector N) :=
  {u | ρ≤|overlap u x|}

theorem poleRegion_measurable {N : ℕ} (x : Vector N) (ρ : ℝ) :
    MeasurableSet (poleRegion x ρ) := by
  apply measurableSet_le measurable_const
  unfold overlap
  fun_prop

theorem uniform_sphere_pole_mass_eventually_le {ρ ε : ℝ}
    (hρ : ρ∈Ioo (0:ℝ) 1) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
      (sphereLaw (n+1)).real (poleRegion x ρ)≤
        Real.exp (((n+1:ℕ):ℝ)*(Real.log (1-ρ^2)/4+ε)) := by
  filter_upwards [partitionOn_eventually_le_of_latitudeProfile_upper hε,
    eventually_ge_atTop (5:ℕ)] with n hlap hn
  intro x hx
  let A : Set ℝ := {r | ρ≤|r|}
  have hA : MeasurableSet A := measurableSet_le measurable_const (continuous_id.abs.measurable)
  have hupper : ∀ r∈A,r∈Ioo (-1:ℝ) 1 → latitudePartitionProfile n 0 (fun _ => 0) x r≤
      Real.log (1-ρ^2)/4 := by
    intro r hr hri
    change ρ≤|r| at hr
    have harg : 0<1-r^2 := by nlinarith [hri.1,hri.2]
    have hρarg : 0<1-ρ^2 := by nlinarith [hρ.1,hρ.2]
    have hlog : Real.log (1-r^2)≤Real.log (1-ρ^2) := by
      apply Real.log_le_log harg
      nlinarith [sq_abs r,hρ.1,abs_nonneg r]
    have hlog0 : Real.log (1-r^2)≤0 := Real.log_nonpos harg.le (by nlinarith [sq_nonneg r])
    have hcoef : (1/4:ℝ)≤((n-2:ℕ):ℝ)/(2*((n+1:ℕ):ℝ)) := by
      rw [Nat.cast_sub (by omega : 2≤n)]
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      apply (le_div_iff₀ (by positivity : 0<(2:ℝ)*((n:ℝ)+1))).mpr
      have hnr : (5:ℝ)≤n := by exact_mod_cast hn
      linarith
    have hh := mul_le_mul_of_nonpos_right hcoef hlog0
    unfold latitudePartitionProfile partitionAgainst
    simp only [zero_mul,Real.exp_zero,integral_const,probReal_univ,one_smul,
      Real.log_one,zero_div,zero_add]
    calc
      _≤(1/4:ℝ)*Real.log (1-r^2) := hh
      _≤(1/4:ℝ)*Real.log (1-ρ^2) := mul_le_mul_of_nonneg_left hlog (by norm_num)
      _=_ := by ring
  have hh := hlap 0 (fun _ => 0) continuous_const x hx A hA
    (Real.log (1-ρ^2)/4) hupper
  have he : partitionOn (0:ℝ) (fun _ : Vector (n+1) => 0) (overlapRegion x A)=
      (sphereLaw (n+1)).real (poleRegion x ρ) := by
    simp only [partitionOn,zero_mul,Real.exp_zero,integral_const,smul_eq_mul,mul_one,Measure.real,
      Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rfl
  rwa [he] at hh

/-- Choose a fixed latitude cutoff above any prescribed interior latitude,
with any prescribed exponential rate, uniformly over all true axes. -/
theorem exists_uniform_sphere_pole_mass_rate {a K : ℝ} (ha : a∈Ico (0:ℝ) 1) (hK : 0<K) :
    ∃ ρ : ℝ,a<ρ ∧ ρ<1 ∧ 0<ρ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
        (sphereLaw (n+1)).real (poleRegion x ρ)≤Real.exp (-K*((n+1:ℕ):ℝ)) := by
  let z := Real.exp (-4*(K+1))
  have hz : 0<z := Real.exp_pos _
  have hz1 : z<1 := by
    change Real.exp (-4*(K+1))<1
    rw [Real.exp_lt_one_iff]
    linarith
  let r := Real.sqrt (1-z)
  have hr : 0<r := Real.sqrt_pos.mpr (by linarith)
  have hrsq : r^2=1-z := Real.sq_sqrt (by linarith : 0≤1-z)
  have hr1 : r<1 := by nlinarith
  let ρ := max r ((a+1)/2)
  have hρ : ρ∈Ioo (0:ℝ) 1 := ⟨hr.trans_le (le_max_left _ _),max_lt hr1 (by linarith [ha.2])⟩
  have haρ : a<ρ := lt_of_lt_of_le (by linarith [ha.2] : a<(a+1)/2) (le_max_right _ _)
  have hρr : r≤ρ := le_max_left _ _
  have hlog : Real.log (1-ρ^2)/4≤-(K+1) := by
    have hh : Real.log (1-ρ^2)≤Real.log z := by
      apply Real.log_le_log (by nlinarith [hρ.1,hρ.2])
      nlinarith
    change Real.log (1-ρ^2)≤Real.log (Real.exp (-4*(K+1))) at hh
    rw [Real.log_exp] at hh
    linarith
  refine ⟨ρ,haρ,hρ.2,hρ.1,?_⟩
  filter_upwards [uniform_sphere_pole_mass_eventually_le hρ (by norm_num : 0<(1:ℝ))] with n hn
  intro x hx
  apply (hn x hx).trans
  apply Real.exp_le_exp.mpr
  have hNp : 0≤((n+1:ℕ):ℝ) := by positivity
  nlinarith

end
end SlowEquilibration.SphericalModel
