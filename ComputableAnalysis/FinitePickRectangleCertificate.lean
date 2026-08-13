import ComputableAnalysis.Basic

namespace ComputableAnalysis

/-!
Parametric Pick certificate for positive axis-aligned lattice rectangles.

This is a reusable finite family rather than a single plotted example.  It
records area, boundary points, and interior points using rational arithmetic
and natural subtraction; no lattice-point measure or completed geometry is
introduced.
-/

def pickRectangleArea (m n : Nat) : Rat := (m : Rat) * n

def pickRectangleBoundary (m n : Nat) : Nat := 2 * m + 2 * n

def pickRectangleInterior (m n : Nat) : Nat := (m - 1) * (n - 1)

theorem pickRectangle_pick_identity {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    pickRectangleArea m n =
      (pickRectangleInterior m n : Rat) +
        (pickRectangleBoundary m n : Rat) / 2 - 1 := by
  dsimp [pickRectangleArea, pickRectangleInterior, pickRectangleBoundary]
  have hm' : 1 ≤ m := by omega
  have hn' : 1 ≤ n := by omega
  have hsubm := Nat.sub_add_cancel hm'
  have hsubn := Nat.sub_add_cancel hn'
  have hnat : m * n + 1 = (m - 1) * (n - 1) + m + n := by
    rw [← hsubm, ← hsubn]
    simp [Nat.add_mul, Nat.mul_add]
    omega
  have hcast : (m : Rat) * (n : Rat) + 1 =
      ((m - 1 : Nat) : Rat) * ((n - 1 : Nat) : Rat) +
        (m : Rat) + (n : Rat) := by
    rw [← Rat.natCast_mul, ← Rat.natCast_mul]
    exact_mod_cast hnat
  rw [show ((2 * m + 2 * n : Nat) : Rat) =
      2 * (m : Rat) + 2 * (n : Rat) by
        simp [Rat.natCast_add, Rat.natCast_mul]]
  rw [Rat.div_def]
  have hden : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem pickRectangle_3_4_certificate :
    pickRectangleArea 3 4 = 12 /\
      pickRectangleBoundary 3 4 = 14 /\
      pickRectangleInterior 3 4 = 6 /\
      pickRectangleArea 3 4 =
        (pickRectangleInterior 3 4 : Rat) +
          (pickRectangleBoundary 3 4 : Rat) / 2 - 1 := by
  native_decide

end ComputableAnalysis
