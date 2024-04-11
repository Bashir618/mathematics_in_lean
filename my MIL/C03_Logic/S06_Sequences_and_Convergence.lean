import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nNsNt
  simp at nNsNt
  rw [add_sub_add_comm]
  calc
    |(s n - a) + (t n - b)| ≤ |s n - a| + |t n - b| := abs_add (s n - a) (t n - b)
    _ < ε / 2 + |t n - b| := add_lt_add_right (hs n nNsNt.1) |t n - b|
    _ < ε / 2 + ε / 2 := add_lt_add_left (ht n nNsNt.2) (ε / 2)
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  have εcpos : (ε / |c| > 0) := div_pos εpos acpos
  obtain t := cs (ε / |c|) εcpos
  simp [← mul_sub c _ a, abs_mul]
  simp [lt_div_iff acpos, mul_comm] at t
  exact t

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngeN
  rw [add_comm]
  calc
    |s n| = |(s n - a) + a| := by congr; ring
    _ ≤ |s n - a| + |a| := abs_add (s n - a) a
    _ < 1 + |a| := add_lt_add_right (h n ngeN) |a|

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngemax
  simp at ngemax
  rw [sub_zero, abs_mul]
  simp [sub_zero] at h₁
  have g₁: |s n| ≤ B := le_of_lt (h₀ n ngemax.1)
  have g₂: |t n| < ε / B := h₁ n ngemax.2
  have Bneq0 : B ≠ 0 := by linarith
  rw [← div_mul_cancel ε Bneq0, mul_comm]
  calc
    |t n| * |s n| ≤ |t n| * B := mul_le_mul_of_nonneg_left g₁ (abs_nonneg t n)
    _ < (ε / B) * B := by rw [mul_lt_mul_right Bpos]; exact g₂

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by simp; contrapose! abne; linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa (max Na Nb) (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb (max Na Nb) (le_max_right Na Nb)
  have : |a - b| < |a - b| := by calc
    |a - b| = |(s N - b) - (s N - a)| := by ring
    _ ≤ |s N - b| + |s N - a| := abs_sub (s N - b) (s N - a)
    _ < ε + ε := by linarith
    _ = 2 * ε := by ring
    _ = 2 * (|a - b| / 2) := by rfl
    _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
