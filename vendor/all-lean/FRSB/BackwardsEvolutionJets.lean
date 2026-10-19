module
public import FRSB.BackwardsJets

@[expose] public section

/-! Exact rational differential-jet computations for the backward Parisi
equation. Each time jet below is the actual differentiated PDE coefficient
in the rescaled backward time; the analytic specialization uses these
explicit identities rather than symbolic differentiation assumptions. -/

noncomputable section
namespace FRSB

def backwardCtJet (a B C D E : ℝ) : ℝ := E / 2 + a * (B * D + C ^ 2)
def backwardDtJet (a B C D E F : ℝ) : ℝ := F / 2 + a * (B * E + 3 * C * D)
def backwardEtJet (a B C D E F G : ℝ) : ℝ := G / 2 + a * (B * F + 4 * C * E + 3 * D ^ 2)
def backwardFtJet (a B C D E F G J : ℝ) : ℝ := J / 2 + a * (B * G + 5 * C * F + 10 * D * E)

def backwardZtJet (C D Ct Dt : ℝ) : ℝ := -Dt / (2 * C) + D * Ct / (2 * C ^ 2)
def backwardPxJet (a C D E F : ℝ) : ℝ :=
  -F / 2 + D * E / C - D ^ 3 / (2 * C ^ 2) - 2 * a * C * D
def backwardPxxJet (a C D E F G : ℝ) : ℝ :=
  -G / 2 + (E ^ 2 + D * F) / C - 5 * D ^ 2 * E / (2 * C ^ 2) + D ^ 4 / C ^ 3 -
    2 * a * (D ^ 2 + C * E)
def backwardPtJet (a C D E Ct Dt Et : ℝ) : ℝ :=
  -Et / 2 + D * Dt / C - D ^ 2 * Ct / (2 * C ^ 2) - 2 * a * C * Ct

def backwardRJet (a C D E F : ℝ) : ℝ :=
  F - 5 * D * E / (2 * C) + 3 * D ^ 3 / (2 * C ^ 2) + 3 * a * C * D
def backwardRxJet (a C D E F G : ℝ) : ℝ :=
  G - 5 * (E ^ 2 + D * F) / (2 * C) + 7 * D ^ 2 * E / C ^ 2 - 3 * D ^ 4 / C ^ 3 +
    3 * a * (D ^ 2 + C * E)
def backwardRxxJet (a C D E F G J : ℝ) : ℝ :=
  J - (15 * E * F + 5 * D * G) / (2 * C) + (33 * D * E ^ 2 + 19 * D ^ 2 * F) / (2 * C ^ 2) -
    26 * D ^ 3 * E / C ^ 3 + 9 * D ^ 5 / C ^ 4 + 3 * a * (3 * D * E + C * F)
def backwardRtJet (a C D E F Ct Dt Et Ft : ℝ) : ℝ :=
  Ft - 5 * (Dt * E + D * Et) / (2 * C) + 5 * D * E * Ct / (2 * C ^ 2) +
    9 * D ^ 2 * Dt / (2 * C ^ 2) - 3 * D ^ 3 * Ct / C ^ 3 + 3 * a * (Ct * D + C * Dt)

theorem backwardRJet_eq_weightedHx (a C D E F : ℝ) (hC : C ≠ 0) :
    backwardRJet a C D E F = C * backwardHxJet a C D E F := by
  dsimp [backwardRJet, backwardHxJet, backwardZJet, backwardZxJet, backwardQxJet, backwardZxxJet]
  field_simp
  ring

theorem backwardPxJet_eq_weightedHx (a C D E F : ℝ) (hC : C ≠ 0) :
    backwardPxJet a C D E F =
      -(C * backwardHxJet a C D E F) / 2 - backwardZJet C D * (C * backwardQJet a C D E) := by
  dsimp [backwardPxJet, backwardHxJet, backwardZJet, backwardZxJet, backwardQxJet, backwardZxxJet, backwardQJet]
  field_simp
  ring

/-- The equation Tz = -2Qz in the genuine differentiated PDE jets. -/
theorem backward_z_evolution_jet (a B C D E F : ℝ) (hC : C ≠ 0) :
    backwardZtJet C D (backwardCtJet a B C D E) (backwardDtJet a B C D E F) -
      backwardZxxJet C D E F / 2 - a * B * backwardZxJet C D E =
      -2 * backwardQJet a C D E * backwardZJet C D := by
  dsimp [backwardZtJet, backwardCtJet, backwardDtJet, backwardZxxJet, backwardZxJet, backwardQJet, backwardZJet]
  field_simp
  ring

/-- The equation T(CQ) = -2Q(CQ). -/
theorem backward_weightedQ_evolution_jet (a B C D E F G : ℝ) (hC : C ≠ 0) :
    backwardPtJet a C D E (backwardCtJet a B C D E)
      (backwardDtJet a B C D E F) (backwardEtJet a B C D E F G) -
      backwardPxxJet a C D E F G / 2 - a * B * backwardPxJet a C D E F =
      -2 * backwardQJet a C D E * (C * backwardQJet a C D E) := by
  dsimp [backwardPtJet, backwardCtJet, backwardDtJet, backwardEtJet, backwardPxxJet, backwardPxJet, backwardQJet, backwardZxJet]
  field_simp
  ring

/-- The equation T(CHx) = -5Q(CHx) + 6CzQ². -/
theorem backward_weightedHx_evolution_jet (a B C D E F G J : ℝ) (hC : C ≠ 0) :
    backwardRtJet a C D E F (backwardCtJet a B C D E) (backwardDtJet a B C D E F)
      (backwardEtJet a B C D E F G) (backwardFtJet a B C D E F G J) -
      backwardRxxJet a C D E F G J / 2 - a * B * backwardRxJet a C D E F G =
      -5 * backwardQJet a C D E * (C * backwardHxJet a C D E F) +
        6 * C * backwardZJet C D * backwardQJet a C D E ^ 2 := by
  rw [← backwardRJet_eq_weightedHx a C D E F hC]
  dsimp [backwardRtJet, backwardCtJet, backwardDtJet, backwardEtJet, backwardFtJet, backwardRxxJet, backwardRxJet, backwardRJet, backwardQJet, backwardZxJet, backwardZJet]
  field_simp
  ring

/-- The five exact source terms used in the scalar comparison induction. -/
theorem backward_barrier_source_algebra (a B C Q z R : ℝ) :
    a * C ^ 2 * (1 - a) + 2 * Q * C * Q + 2 * Q * ((1 - a) * C - C * Q) =
      (1 - a) * C * (a * C + 2 * Q) ∧
    2 * Q * z + 2 * Q * (a * B + 1 - a - z) = 2 * Q * (a * B + 1 - a) ∧
    6 * (1 - a) * (a * C ^ 2) - (-5 * Q * R + 6 * C * z * Q ^ 2) +
      5 * Q * (6 * (1 - a) * C - R) =
      6 * C * ((1 - a) * (a * C + 5 * Q) - z * Q ^ 2) := by
  constructor
  · ring
  constructor <;> ring

theorem backward_last_source_nonneg (a C Q z : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hC : 0 ≤ C) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1 - a)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ 6 * C * ((1 - a) * (a * C + 5 * Q) - z * Q ^ 2) := by
  have hqq : Q ^ 2 ≤ (1 - a) * Q := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hQ1 hQ0
  have hzqq : z * Q ^ 2 ≤ (1 - a) * Q :=
    (mul_le_mul_of_nonneg_right hz1 (sq_nonneg Q)).trans (by simpa using hqq)
  have hac := mul_nonneg ha0 hC
  have haQ := mul_nonneg (sub_nonneg.mpr ha1) hQ0
  have hinner : 0 ≤ (1 - a) * (a * C + 5 * Q) - z * Q ^ 2 := by
    have hca := mul_nonneg (sub_nonneg.mpr ha1) hac
    nlinarith
  exact mul_nonneg (by positivity) hinner

end FRSB
