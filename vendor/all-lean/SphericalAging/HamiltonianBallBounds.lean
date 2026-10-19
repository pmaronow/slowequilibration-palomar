module

public import SphericalAging.LandscapeDerivatives

public section

/-! Actual ordered Hamiltonian energy and overlap bounds on the manuscript
algorithmic ball. No algorithmic threshold or energy ceiling is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.HamiltonianBallBounds
open FiniteModel GaussianLandscape LandscapeDerivatives
open scoped InnerProductSpace

 theorem Hamiltonian_ball_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    (J : Disorder N p) {x : Vector N} (hx : ‖x‖≤Real.sqrt N) :
    |Hamiltonian N p J x|/(N:ℝ)≤landscapeNorm N p J := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hnorm : 0≤normalization N p := Real.rpow_nonneg hNr.le _
  have hform := (tensorForm N p J).le_opNorm (fun _ => x)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hform
  have hh : |Hamiltonian N p J x|≤normalization N p*‖tensorForm N p J‖*‖x‖^p := by
    rw [Hamiltonian_eq_diagonal,abs_mul,abs_of_nonneg hnorm]
    exact (mul_le_mul_of_nonneg_left hform hnorm).trans_eq (by ring)
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hx p)
    (mul_nonneg hnorm (norm_nonneg (tensorForm N p J)))
  have hp' : p=(p-1)+1 := by omega
  have he : normalization N p*‖tensorForm N p J‖*Real.sqrt (N:ℝ)^p=
      ‖tensorForm N p J‖*Real.sqrt (N:ℝ) := by
    calc
      _ = ‖tensorForm N p J‖*(normalization N p*Real.sqrt (N:ℝ)^(p-1))*Real.sqrt (N:ℝ) := by
        conv_lhs => arg 2;rw [hp',pow_succ]
        ring
      _ = _ := by rw [normalization_sqrt_power hN];ring
  rw [he] at hm
  apply (div_le_iff₀ hNr).mpr
  have hb := hh.trans hm
  unfold landscapeNorm
  have hs := Real.mul_self_sqrt hNr.le
  convert hb using 1
  field_simp
  rw [pow_two,hs]

 theorem overlap_abs_le_one {N : ℕ} (hN : 0<N) (w x : Vector N)
    (hw : ‖w‖=Real.sqrt N) (hx : ‖x‖≤Real.sqrt N) :
    |⟪w,x⟫_ℝ/(N:ℝ)|≤1 := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  have hh := (abs_real_inner_le_norm w x).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg w))
  rw [hw,Real.mul_self_sqrt hn.le] at hh
  simpa only [one_mul] using hh

end SphericalAging.HamiltonianBallBounds
