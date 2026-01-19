import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic

namespace ContinuityEngine

open Nat

def prime_list (n : ℕ) : List ℕ :=
  (List.range (n+20)).filter (fun k => Nat.Prime k)

def spiral_coords (primes : List ℕ) (i : ℕ) : (ℕ × ℕ × ℕ × ℕ) :=
  let p := primes.getD (i % primes.length) 2
  let m := 210
  ( (p * i) % m
  , (p^2) % m
  , (p^3) % m
  , (p^4) % m )

def spiral_key (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let primes := prime_list n
  List.range n |>.map (spiral_coords primes)

-- === THEOREM: Periodicity of spiral_coords modulo primes.length ===
theorem spiral_coords_periodic
  (primes : List ℕ) (i : ℕ) (hlen : primes.length > 0) :
  spiral_coords primes i = spiral_coords primes (i + primes.length) := by
  unfold spiral_coords
  simp only [Nat.add_mod_right]

end ContinuityEngine
