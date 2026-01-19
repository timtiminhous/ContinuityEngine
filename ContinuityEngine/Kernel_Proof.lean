import Mathlib

/-!
# ContinuityEngine Kernel Proof
STATUS: VERIFIED
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

def spiral_coords (primes : List ℕ) (m : ℕ) (i : ℕ) : (ℕ × ℕ × ℕ × ℕ) :=
  let p := primes.getD (i % primes.length) 2
  ( (p * i) % m
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
-- We prove that the PRIME p repeats, which is the true cyclic property.
theorem prime_selection_periodic (primes : List ℕ) (i : ℕ) :
  primes.getD (i % primes.length) 2 = primes.getD ((i + primes.length) % primes.length) 2 :=
by
  congr 1
  rw [Nat.add_mod_right]

-- === THEOREM: General Periodicity (Restored & Fixed) ===
-- Proves that adding ANY multiple of the length (k * length) keeps the prime the same.
theorem prime_selection_periodic_general (primes : List ℕ) (i k : ℕ) :
  primes.getD (i % primes.length) 2 = primes.getD ((i + k * primes.length) % primes.length) 2 := by
  congr 1
  -- FIX: Use simp to handle the modulo arithmetic robustly
  simp [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_right]

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
  simp only
  constructor
  · exact Nat.mod_lt _ hm
  constructor
  · exact Nat.mod_lt _ hm
  constructor
  · exact Nat.mod_lt _ hm
  · exact Nat.mod_lt _ hm

end ContinuityEngine
