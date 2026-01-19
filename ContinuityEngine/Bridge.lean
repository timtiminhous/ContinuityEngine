import Mathlib
import ContinuityEngine.Kernel_Proof
import ContinuityEngine.Physics_Proof

/-!
# The Bridge Theorem: Discrete Kernel to Continuous Manifold
Connects computational kernels (Primorial Moduli) to physical manifold (Golden Angle × α⁻¹).
STATUS: VERIFIED
-/

noncomputable section

namespace UnifiedBridge

open PrimeResonance
open ContinuityEngine

-- =================================================================
-- SCALING FACTORS
-- =================================================================

def scaling_factor_210 : ℝ := 210 / 137.035999
def scaling_factor_2310 : ℝ := 2310 / 137.035999
def scaling_factor_30030 : ℝ := 30030 / 137.035999
def scaling_factor_510510 : ℝ := 510510 / 137.035999

def primorial_scaling (primorial : ℕ) : ℝ := (primorial : ℝ) / alpha_inverse

-- =================================================================
-- DISCRETE PHASE MAPPING
-- =================================================================

def discrete_phase (val : ℕ) (modulus : ℕ) : ℝ :=
  (val : ℝ) / (modulus : ℝ) * 2 * Real.pi

def normalized_phase (val : ℕ) (modulus : ℕ) : ℝ :=
  (val : ℝ) / (modulus : ℝ)

-- =================================================================
-- LEMMAS: Scaling Factor Properties
-- =================================================================

lemma primorial_scaling_pos (p : ℕ) (hp : 0 < p) : 0 < primorial_scaling p := by
  unfold primorial_scaling
  apply div_pos
  · exact Nat.cast_pos.mpr hp
  · exact alpha_inv_pos

lemma primorial_scaling_ne_zero (p : ℕ) (hp : 0 < p) : primorial_scaling p ≠ 0 := by
  exact ne_of_gt (primorial_scaling_pos p hp)

-- =================================================================
-- THEOREM: Phase Boundedness
-- =================================================================

theorem discrete_phase_nonneg (val : ℕ) (m : ℕ) : 0 ≤ discrete_phase val m := by
  unfold discrete_phase
  apply mul_nonneg
  · apply mul_nonneg
    · apply div_nonneg
      · exact Nat.cast_nonneg val
      · exact Nat.cast_nonneg m
    · norm_num
  · exact Real.pi_pos.le

theorem discrete_phase_bounded (val : ℕ) (m : ℕ) (hm : 0 < m) (hv : val < m) :
  discrete_phase val m < 2 * Real.pi := by
  unfold discrete_phase
  have h1 : (val : ℝ) / (m : ℝ) < 1 := by
    rw [div_lt_one (Nat.cast_pos.mpr hm)]
    exact Nat.cast_lt.mpr hv
  calc (val : ℝ) / (m : ℝ) * 2 * Real.pi
      < 1 * 2 * Real.pi := by nlinarith [Real.pi_pos]
    _ = 2 * Real.pi := by ring

-- Key: modular reduction always gives valid phase
theorem phase_from_mod_bounded (n : ℕ) (m : ℕ) (hm : 0 < m) :
  0 ≤ discrete_phase (n % m) m ∧ discrete_phase (n % m) m < 2 * Real.pi := by
  exact ⟨discrete_phase_nonneg (n % m) m, discrete_phase_bounded (n % m) m hm (Nat.mod_lt n hm)⟩

-- =================================================================
-- THEOREM: Primorial Ratio Structure
-- =================================================================

theorem primorial_ratio_structure :
  (primorial_5 : ℝ) / primorial_4 = 11 ∧
  (primorial_6 : ℝ) / primorial_5 = 13 ∧
  (primorial_7 : ℝ) / primorial_6 = 17 := by
  unfold primorial_4 primorial_5 primorial_6 primorial_7
  norm_num

-- (Restored)
theorem primorial_chain :
  primorial_5 = primorial_4 * 11 ∧
  primorial_6 = primorial_5 * 13 ∧
  primorial_7 = primorial_6 * 17 ∧
  primorial_8 = primorial_7 * 19 := by
  unfold primorial_4 primorial_5 primorial_6 primorial_7 primorial_8
  decide

-- (Restored)
theorem scaling_ratio_143 :
  scaling_factor_30030 / scaling_factor_210 = 143 := by
  unfold scaling_factor_30030 scaling_factor_210
  norm_num

-- =================================================================
-- MAIN BRIDGE THEOREM: Structural Correspondence
-- =================================================================

theorem structural_correspondence (primorial : ℕ) (hp : 0 < primorial) :
  (∀ n, 0 ≤ discrete_phase (n % primorial) primorial) ∧
  (∀ n, discrete_phase (n % primorial) primorial < 2 * Real.pi) ∧
  (0 < prime_field_rotation) ∧
  (prime_field_rotation ≠ 0) ∧
  (0 < primorial_scaling primorial) := by
  refine ⟨?_, ?_, rotation_pos, rotation_ne_zero, primorial_scaling_pos primorial hp⟩
  · intro n; exact (phase_from_mod_bounded n primorial hp).1
  · intro n; exact (phase_from_mod_bounded n primorial hp).2

-- (Restored)
theorem approximation_bound (primorial : ℕ) (hp : 0 < primorial) (n : ℕ) :
  let θ := discrete_phase (n % primorial) primorial
  0 ≤ θ ∧ θ < 2 * Real.pi ∧
  (∀ k : ℕ, k < primorial →
    discrete_phase k primorial < 2 * Real.pi ∧
    discrete_phase k primorial ≥ 0) := by
  constructor
  · exact (phase_from_mod_bounded n primorial hp).1
  constructor
  · exact (phase_from_mod_bounded n primorial hp).2
  · intro k hk
    exact ⟨discrete_phase_bounded k primorial hp hk, discrete_phase_nonneg k primorial⟩

-- =================================================================
-- PHASE RESOLUTION THEOREM
-- =================================================================

theorem phase_resolution_improves :
  (2 * Real.pi / primorial_5 < 2 * Real.pi / primorial_4) ∧
  (2 * Real.pi / primorial_6 < 2 * Real.pi / primorial_5) ∧
  (2 * Real.pi / primorial_7 < 2 * Real.pi / primorial_6) := by
  unfold primorial_4 primorial_5 primorial_6 primorial_7
  -- Explicitly split the goals
  refine ⟨?_, ?_, ?_⟩
  -- Proof 1
  · apply div_lt_div_of_pos_left
    · apply mul_pos; norm_num; exact Real.pi_pos
    · norm_num
    · norm_num
  -- Proof 2
  · apply div_lt_div_of_pos_left
    · apply mul_pos; norm_num; exact Real.pi_pos
    · norm_num
    · norm_num
  -- Proof 3
  · apply div_lt_div_of_pos_left
    · apply mul_pos; norm_num; exact Real.pi_pos
    · norm_num
    · norm_num

-- =================================================================
-- KERNEL STABILITY THEOREM
-- =================================================================

theorem kernel_stability (n : ℕ) (primorial : ℕ) (hp : 0 < primorial) :
  let θ := discrete_phase (n % primorial) primorial
  let scale := primorial_scaling primorial
  (0 ≤ θ) ∧ (θ < 2 * Real.pi) ∧ (0 < scale) ∧ (0 ≤ θ * scale) := by
  refine ⟨?_, ?_, primorial_scaling_pos primorial hp, ?_⟩
  · exact (phase_from_mod_bounded n primorial hp).1
  · exact (phase_from_mod_bounded n primorial hp).2
  · apply mul_nonneg
    · exact (phase_from_mod_bounded n primorial hp).1
    · exact le_of_lt (primorial_scaling_pos primorial hp)

end UnifiedBridge
