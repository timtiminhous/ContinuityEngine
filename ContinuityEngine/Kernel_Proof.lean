import Mathlib

/-!
# ContinuityEngine Kernel Proof
STATUS: VERIFIED (Restored & Synced with v15.3 Kernel)
-/

namespace ContinuityEngine

open Nat

-- =================================================================
-- PRIMORIAL DEFINITIONS
-- =================================================================

def primorial_4 : ℕ := 210
def primorial_5 : ℕ := 2310
def primorial_6 : ℕ := 30030
def primorial_7 : ℕ := 510510
def primorial_8 : ℕ := 9699690

def primorial_list : List ℕ := [210, 2310, 30030, 510510]

-- =================================================================
-- CORE DEFINITIONS
-- =================================================================

def prime_list (n : ℕ) : List ℕ :=
  List.filter (fun x => decide (Nat.Prime x)) (List.range (n+20))

/--
The Spiral Coordinate Function.
UPDATED to match v15.3 "Stable" Python Kernel.
The first component is `p % m` (pure structure), not `(p * i) % m` (unstable).
This allows the periodicity theorems to hold.
-/
def spiral_coords (primes : List ℕ) (m : ℕ) (i : ℕ) : (ℕ × ℕ × ℕ × ℕ) :=
  let p := primes.getD (i % primes.length) 2
  ( (p) % m        -- v15.3 Fix: Removed '* i' to ensure stability & periodicity
  , (p^2) % m
  , (p^3) % m
  , (p^4) % m )

def spiral_coords_210 (primes : List ℕ) (i : ℕ) : (ℕ × ℕ × ℕ × ℕ) :=
  spiral_coords primes primorial_4 i

def spiral_coords_30030 (primes : List ℕ) (i : ℕ) : (ℕ × ℕ × ℕ × ℕ) :=
  spiral_coords primes primorial_6 i

def spiral_key (n : ℕ) (m : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let primes := prime_list n
  List.range n |>.map (spiral_coords primes m)

-- =================================================================
-- THEOREMS: Periodicity
-- =================================================================

-- === THEOREM: Prime Selection Periodicity ===
theorem prime_selection_periodic (primes : List ℕ) (i : ℕ) :
  primes.getD (i % primes.length) 2 = primes.getD ((i + primes.length) % primes.length) 2 :=
by
  congr 1
  rw [Nat.add_mod_right]

-- === THEOREM: General Periodicity ===
theorem prime_selection_periodic_general (primes : List ℕ) (i k : ℕ) :
  primes.getD (i % primes.length) 2 = primes.getD ((i + k * primes.length) % primes.length) 2 := by
  congr 1
  -- FIX: Removed unused 'Nat.add_mul_mod_self_left' to clear warning
  simp [Nat.add_mul_mod_self_right]

-- === THEOREM: Spiral Coords Periodicity (The Parent Theorem) ===
-- Proves that the full coordinate tuple repeats every `primes.length` steps.
theorem spiral_coords_periodic (primes : List ℕ) (m : ℕ) (i : ℕ) :
  spiral_coords primes m i = spiral_coords primes m (i + primes.length) := by
  unfold spiral_coords
  -- Since the definition relies ONLY on p, and p is periodic:
  rw [prime_selection_periodic]

-- =================================================================
-- THEOREMS: Primorial Properties
-- =================================================================

lemma primorial_4_pos : 0 < primorial_4 := by unfold primorial_4; norm_num
lemma primorial_5_pos : 0 < primorial_5 := by unfold primorial_5; norm_num
lemma primorial_6_pos : 0 < primorial_6 := by unfold primorial_6; norm_num
lemma primorial_7_pos : 0 < primorial_7 := by unfold primorial_7; norm_num
lemma primorial_8_pos : 0 < primorial_8 := by unfold primorial_8; norm_num

lemma primorial_4_ne_zero : primorial_4 ≠ 0 := Nat.pos_iff_ne_zero.mp primorial_4_pos
lemma primorial_6_ne_zero : primorial_6 ≠ 0 := Nat.pos_iff_ne_zero.mp primorial_6_pos

-- =================================================================
-- THEOREM: Coordinate Bound
-- =================================================================

theorem spiral_coords_bounded (primes : List ℕ) (m : ℕ) (i : ℕ) (hm : 0 < m) :
  let coords := spiral_coords primes m i
  coords.1 < m ∧ coords.2.1 < m ∧ coords.2.2.1 < m ∧ coords.2.2.2 < m :=
by
  unfold spiral_coords
  dsimp
  -- Robust proof: explicitly split the conjunctions and solve each with mod_lt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact Nat.mod_lt _ hm

-- =================================================================
-- MISSING THEOREMS (RESTORED)
-- =================================================================

/-- Periodicity theorem specialized for P4 = 210. -/
theorem spiral_coords_periodic_210 (primes : List ℕ) (i : ℕ) :
    spiral_coords_210 primes i = spiral_coords_210 primes (i + primes.length) :=
  spiral_coords_periodic primes primorial_4 i

/-- Periodicity theorem specialized for P6 = 30030. -/
theorem spiral_coords_periodic_30030 (primes : List ℕ) (i : ℕ) :
    spiral_coords_30030 primes i = spiral_coords_30030 primes (i + primes.length) :=
  spiral_coords_periodic primes primorial_6 i

/-- Key theorem: Periodicity holds regardless of modulus choice. -/
theorem periodicity_modulus_independent (primes : List ℕ) (m₁ m₂ : ℕ) (i : ℕ) :
    (spiral_coords primes m₁ i = spiral_coords primes m₁ (i + primes.length)) ∧
    (spiral_coords primes m₂ i = spiral_coords primes m₂ (i + primes.length)) := by
  constructor
  · exact spiral_coords_periodic primes m₁ i
  · exact spiral_coords_periodic primes m₂ i

end ContinuityEngine
