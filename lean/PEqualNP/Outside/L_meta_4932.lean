import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4932

def cols : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]

def rowB (r v : ℕ) : Bool := (cols.getD v 0).getLsbD r

def sel (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : ℕ → Bool
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6
  | 7 => b7
  | 8 => b8
  | 9 => b9
  | 10 => b10
  | 11 => b11
  | 12 => b12
  | 13 => b13
  | _ => false

lemma sel_eq (x : Fin 14 → Bool) (v : Fin 14) : sel (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (↑v) = x v := by
  fin_cases v <;> rfl

lemma edge_off (x : Fin 14 → Bool) (r : ℕ) (a b : Fin 14)
    (hrow : ∀ v : Fin 14, rowB r (↑v) = true → v = a ∨ v = b)
    (h : ¬ (fun v : Fin 14 => rowB r (↑v)) ≤ x) : (x a && x b) = false := by
  by_contra hc
  have hab : x a = true ∧ x b = true := by
    cases hxa : x a <;> cases hxb : x b <;> simp_all
  refine h (Pi.le_def.mpr fun v => ?_)
  show rowB r (↑v) ≤ x v
  cases hv : rowB r (↑v) with
  | false => simp
  | true =>
    rcases hrow v hv with rfl | rfl
    · simp [hab.1]
    · simp [hab.2]

lemma key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool,
    (!(b0 && b7) && !(b0 && b8) && !(b0 && b10) && !(b1 && b7) && !(b1 && b9) && !(b1 && b13) && !(b2 && b8) && !(b2 && b12) && !(b2 && b13) && !(b3 && b7) && !(b3 && b11) && !(b3 && b12) && !(b4 && b10) && !(b4 && b11) && !(b4 && b13) && !(b5 && b9) && !(b5 && b10) && !(b5 && b12) && !(b6 && b8) && !(b6 && b9) && !(b6 && b11)) = true →
    ((List.range 37).any fun k => (List.range 14).all fun v =>
      !(sel b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 v) || rowB (21 + k) v) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_4932

theorem PEqualNP.Outside.L_meta_4932 : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; have x2 : ℕ → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 : Fin (14 : ℕ)) => (x1.getD ↑x3 (0 : BitVec (58 : ℕ))).getLsbD x2; ∀ (x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (21 : ℕ)), ¬x2 ↑x4 ≤ x3) → ∃ (x5 : Fin (37 : ℕ)), x3 ≤ x2 ((21 : ℕ) + ↑x5) := by
  intro x1 x2 x3 h
  have hrows : ∀ r : ℕ, r < 21 →
      ¬ (fun v : Fin 14 => PEqualNP.Outside.L_meta_4932.rowB r (↑v)) ≤ x3 :=
    fun r hr => h ⟨r, hr⟩
  have e0 : (x3 0 && x3 7) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 0 0 7 (by decide +kernel) (hrows 0 (by decide))
  have e1 : (x3 0 && x3 8) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 1 0 8 (by decide +kernel) (hrows 1 (by decide))
  have e2 : (x3 0 && x3 10) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 2 0 10 (by decide +kernel) (hrows 2 (by decide))
  have e3 : (x3 1 && x3 7) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 3 1 7 (by decide +kernel) (hrows 3 (by decide))
  have e4 : (x3 1 && x3 9) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 4 1 9 (by decide +kernel) (hrows 4 (by decide))
  have e5 : (x3 1 && x3 13) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 5 1 13 (by decide +kernel) (hrows 5 (by decide))
  have e6 : (x3 2 && x3 8) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 6 2 8 (by decide +kernel) (hrows 6 (by decide))
  have e7 : (x3 2 && x3 12) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 7 2 12 (by decide +kernel) (hrows 7 (by decide))
  have e8 : (x3 2 && x3 13) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 8 2 13 (by decide +kernel) (hrows 8 (by decide))
  have e9 : (x3 3 && x3 7) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 9 3 7 (by decide +kernel) (hrows 9 (by decide))
  have e10 : (x3 3 && x3 11) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 10 3 11 (by decide +kernel) (hrows 10 (by decide))
  have e11 : (x3 3 && x3 12) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 11 3 12 (by decide +kernel) (hrows 11 (by decide))
  have e12 : (x3 4 && x3 10) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 12 4 10 (by decide +kernel) (hrows 12 (by decide))
  have e13 : (x3 4 && x3 11) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 13 4 11 (by decide +kernel) (hrows 13 (by decide))
  have e14 : (x3 4 && x3 13) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 14 4 13 (by decide +kernel) (hrows 14 (by decide))
  have e15 : (x3 5 && x3 9) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 15 5 9 (by decide +kernel) (hrows 15 (by decide))
  have e16 : (x3 5 && x3 10) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 16 5 10 (by decide +kernel) (hrows 16 (by decide))
  have e17 : (x3 5 && x3 12) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 17 5 12 (by decide +kernel) (hrows 17 (by decide))
  have e18 : (x3 6 && x3 8) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 18 6 8 (by decide +kernel) (hrows 18 (by decide))
  have e19 : (x3 6 && x3 9) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 19 6 9 (by decide +kernel) (hrows 19 (by decide))
  have e20 : (x3 6 && x3 11) = false :=
    PEqualNP.Outside.L_meta_4932.edge_off x3 20 6 11 (by decide +kernel) (hrows 20 (by decide))
  have hK := PEqualNP.Outside.L_meta_4932.key (x3 0) (x3 1) (x3 2) (x3 3) (x3 4) (x3 5) (x3 6) (x3 7) (x3 8) (x3 9) (x3 10) (x3 11) (x3 12) (x3 13)
    (by rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20]; rfl)
  obtain ⟨k, hk, hall⟩ := List.any_eq_true.mp hK
  refine ⟨⟨k, List.mem_range.mp hk⟩, Pi.le_def.mpr fun v => ?_⟩
  show x3 v ≤ PEqualNP.Outside.L_meta_4932.rowB (21 + k) (↑v)
  have hv := List.all_eq_true.mp hall (↑v) (List.mem_range.mpr v.isLt)
  rw [PEqualNP.Outside.L_meta_4932.sel_eq x3 v] at hv
  cases hxv : x3 v with
  | false => simp
  | true =>
    rw [hxv] at hv
    have hr : PEqualNP.Outside.L_meta_4932.rowB (21 + k) (↑v) = true := by simpa using hv
    simp [hr]
