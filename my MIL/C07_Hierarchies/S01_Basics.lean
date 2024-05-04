import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true


class One₁ (α : Type) where
  /-- The element one -/
  one : α


#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one


example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl


class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia


class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)


attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b


class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α


class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α


example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)


example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  have t: a⁻¹ ⋄ a ⋄ b = a⁻¹ ⋄ (a ⋄ b) := dia_assoc a⁻¹ a b
  rw [inv_dia, h] at t
  rw [dia_one, one_dia] at t
  exact t.symm

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have h: (a⁻¹)⁻¹ = a := inv_eq_of_dia (inv_dia a)
  nth_rw 1 [← h]
  exact inv_dia a⁻¹

class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [eq_comm]
  calc
    b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw[Group₃.inv_mul]
    _ = a⁻¹ * (a * b) := mul_assoc₃ a⁻¹ a b
    _ = a⁻¹ * 1 := by rw[h]
    _ = a⁻¹ := mul_one a⁻¹

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  calc
    a * a⁻¹ = 1 * (a * a⁻¹) := by rw[one_mul]
    _ = 1 * a * a⁻¹ := (mul_assoc₃ 1 a a⁻¹).symm
    _ = (a⁻¹⁻¹ * a⁻¹) * a * a⁻¹ := by rw[Group₃.inv_mul]
    _ = a⁻¹⁻¹ * (a⁻¹ * a) * a⁻¹ := by rw[mul_assoc₃ a⁻¹⁻¹ a⁻¹ a]
    _ = a⁻¹⁻¹ * 1 * a⁻¹ := by rw[Group₃.inv_mul]
    _ = a⁻¹⁻¹ * a⁻¹ := by rw[mul_one]
    _ = 1 := Group₃.inv_mul a⁻¹

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  calc
    b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw[Group₃.inv_mul a]
    _ = a⁻¹ * (a * b) := mul_assoc₃ a⁻¹ a b
    _ = a⁻¹ * (a * c) := by rw[h]
    _ = (a⁻¹ * a) * c := (mul_assoc₃ a⁻¹ a c).symm
    _ = 1 * c := by rw[Group₃.inv_mul a]
    _ = c := one_mul c

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  calc
    b = b * 1 := (mul_one b).symm
    _ = b * (a * a⁻¹) := by rw[Group₃.mul_inv]
    _ = (b * a) * a⁻¹ := (mul_assoc₃ b a a⁻¹).symm
    _ = (c * a) * a⁻¹ := by rw[h]
    _ = c * (a * a⁻¹) := mul_assoc₃ c a a⁻¹
    _ = c * 1 := by rw[Group₃.mul_inv]
    _ = c := mul_one c

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G



class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have h : ∀ c : R, -c = (-1) * c := by
      intro c
      apply neg_eq_of_add
      calc
        c + (-1) * c = 1 * c + (-1) * c := by rw[one_mul]
        _ = (1 + (-1)) * c := (Ring₃.right_distrib 1 (-1) c).symm
        _ = 0 * c := by rw[AddGroup₃.add_neg]
        _ = 0 * c + 0 := (add_zero (0 * c)).symm
        _ = 0 * c + (1 * c + -(1 * c)) := by rw[AddGroup₃.add_neg]
        _ = (0 * c + 1 * c) + -(1 * c) := (add_assoc₃ _ _ _).symm
        _ = (0 + 1) * c + -(1 * c) := by rw[Ring₃.right_distrib]
        _ = 1 * c + -(1 * c) := by rw[zero_add]
        _ = 0 := AddGroup₃.add_neg
    calc
      a + b = a + b + 0 := (add_zero (a + b)).symm
      _ = a + b + (-(b + a) + (b + a)) := by rw[AddGroup₃.neg_add]
      _ = (a + b + -(b + a)) + (b + a) := (add_assoc₃ _ _ _).symm
      _ = (a + b + -1 * (b + a)) + (b + a) := by rw[h (b + a)]
      _ = (a + b + (-1 * b + -1 * a)) + (b + a) := by rw[Ring₃.left_distrib]
      _ = (a + b + (-b + -a)) + (b + a) := by rw[← h b, ← h a]
      _ = (a + (b + -b + -a)) + (b + a) := by rw[add_assoc₃ a b _, ← add_assoc₃ b _ _]
      _ = (a + (0 + -a)) + (b + a) := by rw[AddGroup₃.add_neg]
      _ = (a + -a) + (b + a) := by rw[zero_add]
      _ = 0 + (b + a) := by rw[AddGroup₃.add_neg]
      _ = b + a := zero_add (b + a) }

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type) extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ {a b c : α} (_ : a ≤₁ b) (_ : b ≤₁ c), a ≤₁ c

class PartialOrder₁ (α : Type) extends Preorder₁ α where
  le_antisymm : ∀ {a b : α} (_ : a ≤₁ b) (_ : b ≤₁ a), a = b

class OrderedCommMonoid₁ (α : Type) extends CommMonoid₃ α, PartialOrder₁ α where
  mul_le_of_le {a b : α} (_ : a ≤₁ b) : ∀ c : α, c * a ≤₁ c * b

instance : OrderedCommMonoid₁ ℕ where
  le := (· ≤ ·)
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  mul := (· * ·)
  mul_assoc₃ := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  le_antisymm := Nat.le_antisymm
  mul_le_of_le := by
    intro a b h c
    exact Nat.mul_le_mul Nat.le.refl h

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul


class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

#synth Module₁ ℤ ℤ -- abGrpModule ℤ


class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
