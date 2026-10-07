# lean-practice

My Lean 4 practice set. Every file compiles: if `lake build` passes, the proofs are right. That is the whole grading system.

## Setup

1. Install Lean via [elan](https://github.com/leanprover/elan):
   ```
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```
2. Clone this repo and fetch the math library:
   ```
   git clone https://github.com/absolukie/lean-practice
   cd lean-practice
   lake update
   lake exe cache get
   ```
3. Check your work:
   ```
   lake build
   ```

## The files

- `LeanPractice/Basics.lean` — start here. Tactics from zero: `rfl`, `exact`, `intro`, `constructor`, `induction`, `decide`. Ends with three exercises using `sorry` for you to fill in.
- `LeanPractice/Irrational.lean` — the showpiece: √2 is irrational, proved from scratch and checked by the computer. Heavily commented. The number-theoretic heart (`no_reduced_sqrt2`) is pure arithmetic; the wrapper connects it to `Real.sqrt` via lowest-terms fractions. Ends with two exercises (in comments, so the file keeps compiling): √3, then √p for any prime p.

## Working on the exercises

Uncomment an exercise, replace the `sorry` with your proof, run `lake env lean LeanPractice/Irrational.lean`. No errors means you got it right.

## Why this exists

OpenAI released [722 math manuscripts](https://github.com/openai/math) from an unreleased model, some with Lean formalizations. Those proofs are research-level. This is the trailhead: the 2,500-year-old proof that √2 is not a fraction, in a form a computer can check.
