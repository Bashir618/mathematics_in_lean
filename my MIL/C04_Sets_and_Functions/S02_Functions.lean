import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro fsv
    intro x xs
    simp
    have fxfs : f x ∈ f '' s := by simp; use x, xs
    exact fsv fxfs
  · intro sfv
    intro x ⟨y, ys, xfy⟩
    have fyv : f y ∈ v := sfv ys
    rw [xfy] at fyv
    exact fyv

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xffs
  simp at xffs
  obtain ⟨y, ys, fyfx⟩ := xffs
  have yeqx: y = x := h fyfx
  rw [yeqx] at ys
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x xffu
  simp at xffu
  obtain ⟨y, fyu, fyx⟩ := xffu
  rw [fyx] at fyu
  exact fyu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xu
  obtain ⟨y, fyx⟩ := h x
  simp
  use y
  rw [fyx]
  exact ⟨xu, rfl⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x ⟨y, ys, fyx⟩
  use y
  exact ⟨h ys, fyx⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
  fun _ xfu ↦ h xfu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  fun _ ⟨y, yst, fyx⟩ ↦ ⟨⟨y, yst.1, fyx⟩, ⟨y, yst.2, fyx⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x ⟨xfs, xft⟩
  obtain ⟨y₁, ys, fy₁x⟩ := xfs
  obtain ⟨y₂, yt, fy₂x⟩ := xft
  rw [← fy₂x] at fy₁x
  have : y₁ = y₂ := h fy₁x
  rw [← this] at yt fy₂x
  exact ⟨y₁, ⟨ys, yt⟩, fy₂x⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x ⟨xfs, xnft⟩
  obtain ⟨y, ys, fyx⟩ := xfs
  use y
  constructor
  · use ys
    contrapose! xnft
    exact ⟨y, xnft, fyx⟩
  · exact fyx

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun _ ⟨xfu, xnfv⟩ ↦ ⟨xfu, xnfv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  · intro ⟨⟨y, ys, fyx⟩, xv⟩
    use y
    constructor
    · use ys
      rw [← fyx] at xv
      exact xv
    · exact fyx
  · intro ⟨y, ys, fyx⟩
    constructor
    · exact ⟨y, ys.1, fyx⟩
    · rw [← fyx]
      exact ys.2

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x ⟨y, ysfu, fyx⟩
  constructor
  · use y
    exact ⟨ysfu.1, fyx⟩
  · rw [← fyx]
    exact ysfu.2

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
  fun x ⟨xs, fxu⟩ ↦ ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · exact Or.inl ⟨x, xs, rfl⟩
  · exact Or.inr fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  · intro ⟨y, yA, fyx⟩
    simp at yA
    obtain ⟨i, yAi⟩ := yA
    simp
    use i
    exact ⟨y, yAi, fyx⟩
  · intro xfA
    rw [mem_iUnion] at xfA
    obtain ⟨i, xfAi⟩ := xfA
    obtain ⟨y, yAi, fyx⟩ := xfAi
    use y
    rw [mem_iUnion]
    exact ⟨⟨i, yAi⟩, fyx⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x xfA
  obtain ⟨y, yA, fyx⟩ := xfA
  rw [mem_iInter]
  intro i
  use y
  simp at yA
  exact ⟨yA i, fyx⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x xfA
  rw [mem_iInter] at xfA
  obtain ⟨y, _, fyx⟩ := xfA i
  use y
  constructor
  · simp
    intro j
    obtain ⟨z, zAj, fzx⟩ := xfA j
    rw [← fzx] at fyx
    rw [injf fyx]
    exact zAj
  · exact fyx

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnng y ynng sqrtxeqsqrty
  calc
    x = (sqrt x) ^ 2 := (sq_sqrt xnng).symm
    _ = (sqrt y) ^ 2 := by rw [sqrtxeqsqrty]
    _ = y := sq_sqrt ynng

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnng y ynng sqxeqsqy
  simp at sqxeqsqy
  calc
    x = sqrt (x ^ 2) := (sqrt_sq xnng).symm
    _ = sqrt (y ^ 2) := by rw [sqxeqsqy]
    _ = y := sqrt_sq ynng

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  · intro ⟨x, _, fxy⟩
    rw [← fxy]
    exact sqrt_nonneg x
  · intro ynng
    use y ^ 2
    use pow_two_nonneg y
    exact sqrt_sq ynng

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · intro ⟨x, fxy⟩
    rw [← fxy]
    exact pow_two_nonneg x
  · intro ynng
    use sqrt y
    exact sq_sqrt ynng

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf
    intro x
    apply injf
    have h: ∃ y, f y = f x := by use x
    exact inverse_spec (f x) h
  · intro linvf
    intro x y fxfy
    rw [← linvf x, ← linvf y]
    rw [fxfy]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjf
    intro y
    exact inverse_spec y (surjf y)
  · intro rinvf
    intro y
    rw [← rinvf y]
    use inverse f y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rw [← h]; exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
