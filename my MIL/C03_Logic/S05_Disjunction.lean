import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · calc
      x ≤ 0 := le_of_lt h
      _ ≤ |x| := abs_nonneg x

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · calc
      -x ≤ 0 := neg_nonpos_of_nonneg h
      _ ≤ |x| := abs_nonneg x
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor
  · rw [neg_le, neg_add]
    calc
      -x + -y ≤ |x| + -y := add_le_add_right (neg_le_abs_self x) (-y)
      _ ≤ |x| + |y| := add_le_add_left (neg_le_abs_self y) |x|
  · calc
      x + y ≤ |x| + y := add_le_add_right (le_abs_self x) y
      _ ≤ |x| + |y| := add_le_add_left (le_abs_self y) |x|

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    rcases le_or_gt 0 y with t | t
    · left
      rw [abs_of_nonneg t] at h
      exact h
    · right
      rw [abs_of_neg t] at h
      exact h
  · intro h
    rcases h with t | t
    · calc
        x < y := t
        _ ≤ |y| := le_abs_self y
    · calc
        x < -y := t
        _ ≤ |y| := neg_le_abs_self y

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    constructor
    · have : -x < y := lt_of_le_of_lt (neg_le_abs_self x) h
      rw [neg_lt]
      exact this
    · have : x < y := lt_of_le_of_lt (le_abs_self x) h
      exact this
  · intro ⟨h₁, h₂⟩
    rcases le_or_gt 0 x with t | t
    · rw [abs_of_nonneg t]
      exact h₂
    · rw [abs_of_neg t]
      rw [neg_lt]
      exact h₁

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  obtain ⟨x, y, t⟩ := h; rcases t with _ | _; repeat linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with t | t
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with t | t
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by ring; rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with t | t
  · left; rw [← sub_zero x, ← t]; ring
  · right; rw [← sub_zero x, ← t]; ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by ring; rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with t | t
  · left; rw [← sub_zero x, ← t]; ring
  · right; rw [← sub_zero x, ← t]; ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases t : P
    · right; exact h t
    · left; exact t
  · intro h p
    rcases h with t | t
    · contradiction
    · exact t
