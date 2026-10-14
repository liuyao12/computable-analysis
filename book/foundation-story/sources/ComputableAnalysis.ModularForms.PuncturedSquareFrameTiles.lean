import ComputableAnalysis.ModularForms.PuncturedKernelGridBoundaryVanishing
import ComputableAnalysis.ModularForms.RepresentedGridFrame

/-! A concrete twelve-tile square frame with a justified central hole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Four equal coordinate intervals spanning the outer square. -/
def squareFrameInterval (R : QPos) (j : Nat) : QInterval :=
  ⟨-2*R.val+(j:Rat)*R.val,-2*R.val+((j+1:Nat):Rat)*R.val⟩

def squareFrameTile (R : QPos) (j k : Nat) : QInterval × QInterval :=
  (squareFrameInterval R j,squareFrameInterval R k)

/-- Exactly the surrounding twelve tiles of the four by four square. -/
def squareFrameTileIndex (j k : Nat) : Prop :=
  j<4 ∧ k<4 ∧ (j=0 ∨ j=3 ∨ k=0 ∨ k=3)

theorem squareFrameTile_ordered (R : QPos) (j k : Nat) :
    (squareFrameTile R j k).1.lo≤(squareFrameTile R j k).1.hi ∧
      (squareFrameTile R j k).2.lo≤(squareFrameTile R j k).2.hi := by
  have hp := R.property
  simp only [squareFrameTile,squareFrameInterval,Rat.natCast_add]
  constructor <;> change -2*R.val+_ *R.val≤ -2*R.val+(_+1)*R.val <;> grind only

theorem squareFrameTile_separated (R : QPos) (j k : Nat)
    (h : squareFrameTileIndex j k) : rectangleSeparated (squareFrameTile R j k) R := by
  rcases h.2.2 with hj|hj|hk|hk
  · subst j
    apply Or.inr; apply Or.inl
    change -2*R.val+1*R.val≤ -R.val
    grind only
  · subst j
    apply Or.inl
    change R.val≤ -2*R.val+3*R.val
    grind only
  · subst k
    apply Or.inr; apply Or.inr; apply Or.inr
    change -2*R.val+1*R.val≤ -R.val
    grind only
  · subst k
    apply Or.inr; apply Or.inr; apply Or.inl
    change R.val≤ -2*R.val+3*R.val
    grind only

theorem puncturedKernel_squareFrameTile_boundary_converges_zero (c : Scalar)
    (R eps : QPos) (j k : Nat) (h : squareFrameTileIndex j k) :
    ∃ N, ∀ n, N≤n →
      Small (puncturedKernelGridBoundary c (squareFrameTile R j k) n).val eps.val := by
  have ho := squareFrameTile_ordered R j k
  exact puncturedKernelGridBoundary_converges_zero c R (squareFrameTile R j k)
    (squareFrameTile_separated R j k h) ho.1 ho.2 eps

theorem finite_eventual_depth (P : Nat → Nat → Prop) (m : Nat)
    (h : ∀ j, j<m → ∃ N, ∀ n, N≤n → P j n) :
    ∃ N, ∀ n, N≤n → ∀ j, j<m → P j n := by
  induction m with
  | zero => exact ⟨0,by intro n hn j hj; omega⟩
  | succ m ih =>
    obtain ⟨A,hA⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨B,hB⟩ := h m (by omega)
    refine ⟨A+B, ?_⟩
    intro n hn j hj
    by_cases he : j=m
    · subst j; exact hB n (by omega)
    · exact hA n (by omega) j (by omega)

theorem puncturedKernel_squareFrame_uniform_depth (c : Scalar) (R eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ j k, squareFrameTileIndex j k →
      Small (puncturedKernelGridBoundary c (squareFrameTile R j k) n).val eps.val := by
  have h : ∀ j, j<4 → ∃ N, ∀ n, N≤n → ∀ k, k<4 →
      squareFrameTileIndex j k →
      Small (puncturedKernelGridBoundary c (squareFrameTile R j k) n).val eps.val := by
    intro j hj
    apply finite_eventual_depth
    intro k hk
    by_cases hf : squareFrameTileIndex j k
    · obtain ⟨N,hN⟩ := puncturedKernel_squareFrameTile_boundary_converges_zero c R eps j k hf
      exact ⟨N,fun n hn _ => hN n hn⟩
    · exact ⟨0,by intro n hn hh; exact False.elim (hf hh)⟩
  obtain ⟨N,hN⟩ := finite_eventual_depth _ 4 h
  exact ⟨N,fun n hn j k hf => hN n hn j hf.1 k hf.2.1 hf⟩

def puncturedKernel_squareFrameBoundarySum (c : Scalar) (R : QPos) (n : Nat) : Scalar :=
  frameScalarSum (fun j k => puncturedKernelGridBoundary c (squareFrameTile R j k) n) 1 2 1 1 2 1

theorem puncturedKernel_squareFrameBoundarySum_converges_zero (c : Scalar) (R eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (puncturedKernel_squareFrameBoundarySum c R n).val eps.val := by
  let eta : QPos := ⟨eps.val/12,by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨N,hN⟩ := puncturedKernel_squareFrame_uniform_depth c R eta
  refine ⟨N, ?_⟩
  intro n hn
  have hb := frameScalarSum_bound
    (fun j k => puncturedKernelGridBoundary c (squareFrameTile R j k) n)
    1 2 1 1 2 1 eta.val (Rat.le_of_lt eta.property) (by
      intro j k hf
      have hi : squareFrameTileIndex j k := by
        unfold representedFrameCell at hf
        unfold squareFrameTileIndex
        omega
      exact hN n hn j k hi)
  have he : ((representedFrameCellCount 1 2 1 1 2 1:Nat):Rat)*eta.val=eps.val := by
    change 12*(eps.val/12)=eps.val
    grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms


