import Mathlib.Data.Real.Basic
import ContinuityEngine.Physics_Proof

namespace UnifiedBridge

open PrimeResonance

/--
**The Edginian Conservation Law**:
Formal proof that if a single resonance node (zero) z lies between
integers n and n+2, the sum of distances is exactly 2.
-/
theorem edginian_conservation_law
  (n : ℝ) (z : ℝ)
  (h_lower : n ≤ z)
  (h_upper : z ≤ n + 2) :
  |z - n| + |z - (n + 2)| = 2 := by
  -- 1. Handle the first term: |z - n|. Since n ≤ z, z - n is non-negative.
  rw [abs_of_nonneg (by linarith)]
  
  -- 2. Handle the second term: |z - (n + 2)|.
  -- Since z ≤ n + 2, the term (z - (n + 2)) is negative or zero.
  -- We use the property |a - b| = |b - a| to flip it to ((n + 2) - z), which is positive.
  rw [abs_sub_comm z (n + 2)]
  
  -- 3. Now we can drop the absolute value bars because (n + 2) - z ≥ 0.
  rw [abs_of_nonneg (by linarith)]
  
  -- 4. Simple algebra: (z - n) + (n + 2 - z) = 2
  ring

/--
**The Breaking of Conservation (The Threshold)**:
If the zero z is NOT between n and n+2 (i.e., the "Chaotic Regime"
where density forces z outside), the sum is strictly greater than 2.
-/
theorem conservation_breaking
  (n : ℝ) (z : ℝ)
  (h_outside : z > n + 2) :
  |z - n| + |z - (n + 2)| > 2 := by
  -- 1. Since z > n + 2 > n, both terms inside absolute values are strictly positive.
  rw [abs_of_pos (by linarith)]
  rw [abs_of_pos (by linarith)]
  
  -- 2. The expression becomes (z - n) + (z - (n + 2)) = 2z - 2n - 2.
  -- We need to prove 2z - 2n - 2 > 2.
  -- Given z > n + 2, linarith can solve this automatically.
  linarith
  
 -- The DIFF = 2 case (zero OUTSIDE [n, n+2])
-- When the same zero serves both integers but lies outside the interval
theorem edginian_conservation_diff (n z : ℝ) (h_outside : z < n ∨ z > n + 2) : 
    |abs (z - n) - abs (z - (n + 2))| = 2 := by
  cases h_outside with
  | inl h_below =>  -- z < n case
    have h1 : z - n < 0 := by linarith
    have h2 : z - (n + 2) < 0 := by linarith
    rw [abs_of_neg h1, abs_of_neg h2]
    ring_nf
    norm_num
  | inr h_above =>  -- z > n + 2 case
    have h1 : z - n > 0 := by linarith
    have h2 : z - (n + 2) > 0 := by linarith
    rw [abs_of_pos h1, abs_of_pos h2]
    ring_nf
    norm_num

end UnifiedBridge
