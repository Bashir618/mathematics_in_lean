import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · exact inf_le_right
    · exact inf_le_left
  · apply le_inf
    · exact inf_le_right
    · exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · calc
      x ⊓ y ⊓ z ≤ x ⊓ y := inf_le_left
      _ ≤ x := inf_le_left
    · apply le_inf
      · calc
        x ⊓ y ⊓ z ≤ x ⊓ y := inf_le_left
        _ ≤ y := inf_le_right
      · exact inf_le_right
  · apply le_inf
    · apply le_inf
      · exact inf_le_left
      · calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
        _ ≤ y := inf_le_left
    · calc
      x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
      _ ≤ z := inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_left
      · calc
        y ≤ y ⊔ z := le_sup_left
        _ ≤ x ⊔ (y ⊔ z) := le_sup_right
    · calc
      z ≤ y ⊔ z := le_sup_right
      _ ≤ x ⊔ (y ⊔ z) := le_sup_right
  · apply sup_le
    · calc
        x ≤ x ⊔ y := le_sup_left
        _ ≤ (x ⊔ y) ⊔ z := le_sup_left
    · apply sup_le
      · calc
        y ≤ x ⊔ y := le_sup_right
        _ ≤ x ⊔ y ⊔ z := le_sup_left
      · exact le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left
  · apply le_inf
    · exact le_refl x
    · exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · exact le_refl x
    · exact inf_le_left
  · exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · apply le_inf
    · apply sup_le
      · exact le_sup_left
      · calc
        b ⊓ c ≤ b := inf_le_left
        _ ≤ a ⊔ b := le_sup_right
    · apply sup_le
      · exact le_sup_left
      · calc
        b ⊓ c ≤ c := inf_le_right
        _ ≤ a ⊔ c := le_sup_right
  · have t: (a ⊓ b) ⊔ (c ⊓ b) ≤ a ⊔ (b ⊓ c) := by
      apply sup_le
      · calc
        a ⊓ b ≤ a := inf_le_left
        _ ≤ a ⊔ (b ⊓ c) := le_sup_left
      · rw [inf_comm]
        exact le_sup_right
    nth_rw 1 [inf_comm] at t
    nth_rw 2 [inf_comm] at t
    rw [← h] at t
    rw [inf_comm] at t

    rw [inf_comm]
    rw [h]
    rw [inf_comm]
    rw [inf_sup_self]
    apply sup_le
    · exact le_sup_left
    · exact t

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  · rw [h]
    nth_rw 2 [sup_comm]
    rw [sup_inf_self]
    apply le_inf
    · exact inf_le_left
    · nth_rw 2 [sup_comm]
      rw [h]
      rw [sup_comm]
      apply le_inf
      · calc
        a ⊓ (c ⊔ b) ≤ a := inf_le_left
        _ ≤ c ⊔ a := le_sup_right
      · exact inf_le_right
  · apply sup_le
    · apply le_inf
      · exact inf_le_left
      · calc
        a ⊓ b ≤ b := inf_le_right
        _ ≤ b ⊔ c := le_sup_left
    · apply le_inf
      · exact inf_le_left
      · calc
        a ⊓ c ≤ c := inf_le_right
        _ ≤ b ⊔ c := le_sup_right

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have t: -a + a ≤ -a + b := add_le_add_left h (-a)
  rw [add_comm, add_neg_self] at t
  rw [add_comm, ← sub_eq_add_neg] at t
  exact t

example (h: 0 ≤ b - a) : a ≤ b := by
  have t: a + 0 ≤ a + (b - a) := add_le_add_left h a
  rw [add_zero, add_sub] at t
  rw [add_comm, ← add_sub, sub_self, add_zero] at t
  exact t

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have t₁: -a + a ≤ -a + b := add_le_add_left h (-a)
  rw [add_comm, add_neg_self] at t₁
  rw [add_comm, ← sub_eq_add_neg] at t₁
  have t₂: 0 ≤ (b - a) * c := mul_nonneg t₁ h'
  rw [sub_mul] at t₂
  have t: a * c + 0 ≤ a * c + (b * c - a * c) := add_le_add_left t₂ (a * c)
  rw [add_zero, add_sub] at t
  rw [add_comm, ← add_sub, sub_self, add_zero] at t
  exact t
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  apply nonneg_of_mul_nonneg_left
  calc
    0 = dist x x := by rw [dist_self x]
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ ≤ dist x y + dist x y := by rw [dist_comm]
    _ = (dist x y) * 2 := by rw [← two_mul, mul_comm]
  exact two_pos

end
