/-
# Lean Practice: Why √2 is irrational

This is the on-ramp to what the OpenAI math release is about.
One of their headline families is the *irrationality exponent of π*:
how well π can be approximated by fractions. That proof lives far up
the mountain. This is base camp: the 2,500-year-old proof that √2 is
irrational, checked by a computer, one step at a time.

The strategy is proof by contradiction:
1. Suppose √2 = a/b for some integers a, b (b ≠ 0).
2. Square both sides: a² = 2b².
3. Reduce the fraction to lowest terms: p/q with p, q coprime.
4. From p² = 2q²: 2 divides p², and 2 is prime, so 2 divides p.
5. Write p = 2k. Then 2q² = 4k², so q² = 2k², so 2 divides q.
6. But 2 dividing both p and q contradicts "lowest terms". Done.

Steps 4-6 are pure arithmetic about natural numbers, no real numbers
involved. That's `no_reduced_sqrt2` below: the heart of the proof.
The second theorem connects it to √2 itself.
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic

-- The number-theoretic heart. No real numbers, no fractions:
-- you cannot have p² = 2q² with p and q coprime.
theorem no_reduced_sqrt2 (p q : ℕ) (hcop : Nat.Coprime p q)
    (h : p ^ 2 = 2 * q ^ 2) : False := by
  -- Step 4: 2 ∣ p², and 2 is prime, so 2 ∣ p.
  have h2p : 2 ∣ p := by
    have hdiv : 2 ∣ p ^ 2 := ⟨q ^ 2, h⟩
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdiv
  -- Step 5: write p = 2k, substitute, and simplify to q² = 2k².
  obtain ⟨k, hk⟩ := h2p
  have hqk : q ^ 2 = 2 * k ^ 2 := by
    have h1 : (2 * k) ^ 2 = 2 * q ^ 2 := by rw [← hk]; exact h
    have h2 : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    omega
  -- Step 5b: same prime argument gives 2 ∣ q.
  have h2q : 2 ∣ q := by
    have hdiv : 2 ∣ q ^ 2 := ⟨k ^ 2, hqk⟩
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdiv
  -- Step 6: 2 divides gcd p q, but gcd p q = 1. Contradiction.
  have hgcd : 2 ∣ Nat.gcd p q := Nat.dvd_gcd ⟨k, hk⟩ h2q
  have hone : Nat.gcd p q = 1 := hcop
  rw [hone] at hgcd
  exact absurd hgcd (by decide)

-- The showpiece: √2 is irrational.
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb h
  -- h : √(2) = (a : ℝ) / (b : ℝ), with (b : ℝ) ≠ 0.
  -- Reduce to lowest terms using the rational q = a/b.
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  set q : ℚ := (a : ℚ) / (b : ℚ) with hqdef
  have hred : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hden : q.den ≠ 0 := q.den_nz
  -- Rewrite the assumption in lowest terms: √(2) = q.num / q.den.
  have hmain : (Real.sqrt 2) = (((q.num : ℚ) / (q.den : ℚ)) : ℝ) := by
    have h2 : ((((q.num : ℚ) / (q.den : ℚ)) : ℝ)) = ((q : ℚ) : ℝ) := by
      exact_mod_cast Rat.num_div_den q
    rw [h2, hqdef, Rat.cast_div]
    exact_mod_cast h
  -- Square both sides and clear denominators: q.num² = 2 * q.den² over ℤ.
  have hZ : (q.num : ℤ) ^ 2 = 2 * (q.den : ℤ) ^ 2 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsq : ((((q.num : ℚ) / (q.den : ℚ)) : ℝ)) ^ 2 = 2 := by
      rw [← hmain]; exact h2
    have hdenR : ((((q.den : ℚ)) : ℝ)) ≠ 0 := by exact_mod_cast hden
    rw [div_pow] at hsq
    have hcleared : ((((q.num : ℚ)) : ℝ)) ^ 2 = 2 * ((((q.den : ℚ)) : ℝ)) ^ 2 := by
      have hdiv := (div_eq_iff (pow_ne_zero 2 hdenR)).mp hsq
      linarith [hdiv]
    exact_mod_cast hcleared
  -- Squares erase signs: move to ℕ via natAbs.
  have hN : q.num.natAbs ^ 2 = 2 * q.den ^ 2 := by
    have hA := congrArg Int.natAbs hZ
    rw [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_natCast] at hA
    exact hA
  exact no_reduced_sqrt2 q.num.natAbs q.den hred hN

/-
## Your turn

Exercise 1: the same proof works for √3. Only the prime changes.
(Hint: every `2` in `no_reduced_sqrt2` becomes `3`. The wrapper
needs `Real.sq_sqrt` with `0 ≤ 3` and the same lowest-terms steps.)

theorem sqrt_three_irrational : Irrational (Real.sqrt 3) := by
  sorry

Exercise 2 (challenge): generalize. For any prime p,
√p is irrational. You will need `Nat.Prime.dvd_of_dvd_pow hp`
instead of the hardcoded prime 2.

theorem sqrt_prime_irrational (p : ℕ) (hp : p.Prime) :
    Irrational (Real.sqrt p) := by
  sorry
-/
