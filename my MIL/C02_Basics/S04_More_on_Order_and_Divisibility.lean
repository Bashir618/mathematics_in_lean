import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · exact le_max_right b a
    exact le_max_left b a
  · show max b a ≤ max a b
    apply max_le
    · exact le_max_right a b
    exact le_max_left a b

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · have h: min (min a b) c ≤ min a b := by apply min_le_left
      apply le_trans h
      exact min_le_left a b
    · apply le_min
      · have h: min (min a b) c ≤ min a b := by apply min_le_left
        apply le_trans h
        exact min_le_right a b
      · exact min_le_right (min a b) c
  · apply le_min
    · apply le_min
      · exact min_le_left a (min b c)
      · have h: min a (min b c) ≤ min b c := by apply min_le_right
        apply le_trans h
        exact min_le_left b c
    · have h: min a (min b c) ≤ min b c := by apply min_le_right
      apply le_trans h
      exact min_le_right b c

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    exact min_le_left a b
  · apply add_le_add_right
    exact min_le_right a b

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · rw [← add_neg_cancel_right (min (a + c) (b + c)) (-c)]
    rw [neg_neg]
    apply add_le_add_right
    nth_rw 2 [← add_neg_cancel_right a c]
    nth_rw 2 [← add_neg_cancel_right b c]
    exact aux (a + c) (b + c) (-c)

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  suffices h: |a| ≤ |a - b| + |b| by linarith
  nth_rw 1 [← add_neg_cancel_right a (-b)]
  rw [neg_neg]
  exact abs_add (a - b) b
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      exact dvd_mul_right x z
    · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right
    exact h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  · apply dvd_gcd
    · exact gcd_dvd_right m n
    · exact gcd_dvd_left m n
  · apply dvd_gcd
    · exact gcd_dvd_right n m
    · exact gcd_dvd_left n m

end
