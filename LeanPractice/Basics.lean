/-
# Lean Practice: Basics

Welcome. Each block below is a tiny proof. Read the comment,
then read the proof. The `#check` lines let you hover and see types.

To work through these yourself: replace a proof with `sorry`,
then try to rebuild it. Lean will tell you exactly what's left.
-/

-- 1. The simplest proof: two things that compute to the same value.
-- `rfl` means "these are equal by definition".
example : 2 + 2 = 4 := rfl

-- 2. A proof is just a function. If you have evidence for P,
-- you have evidence for P.
example (P : Prop) (h : P) : P := h

-- 3. Implication is a function: feed it evidence for P,
-- get evidence for Q.
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP

-- 4. To prove `P ∧ Q`, prove both parts. The angle brackets
-- build the pair.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨hP, hQ⟩

-- 5. To use `P ∧ Q`, split it apart with `obtain`.
example (P Q R : Prop) (hPQ : P ∧ Q) (hQR : Q → R) : P ∧ R := by
  obtain ⟨hP, hQ⟩ := hPQ
  exact ⟨hP, hQR hQ⟩

-- 6. Induction: to prove something for all natural numbers,
-- prove it for zero, then prove the step.
-- Adding zero on the right needs no induction at all:
-- `n + 0` computes to `n` straight from the definition of `+`.
-- (This is exactly why #7, zero on the left, is harder.)
theorem add_zero' (n : Nat) : n + 0 = n := rfl

-- 7. Adding zero on the LEFT needs induction too,
-- because `0 + n` does not compute directly.
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- 8. `decide` proves decidable facts by computation.
-- Lean just runs the program.
example : 3 < 7 := by decide
example : ¬ (5 = 6) := by decide

/-
## Your turn

Replace each `sorry` below and make the file compile.
`lake build` checks your work. There is no partial credit
in Lean: it compiles or it doesn't, and the error tells you why.
-/

-- Exercise 1: prove the reverse direction of #4.
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  sorry

-- Exercise 2: triple nesting, just functions all the way down.
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hP : P) : R := by
  sorry

-- Exercise 3: induction again. Hint: mirror #7.
theorem succ_add' (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  sorry
