import ComputableAnalysis.RiemannHilbert.ContourFixedSampler

/-! Finitely many actual holomorphic annuli transfer the fixed outer
boundary to an arbitrarily small inner boundary. Mesh shifts are accounted
for exactly, and the finite-cover arguments stay inside proofs. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem shrinkingContourRadius_double_next (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) :
    doubleContourRadius (shrinkingContourRadius f hf a ha (m+1))=shrinkingContourRadius f hf a ha m := by
  apply Subtype.ext
  change 2*((contourBaseRadius f hf a ha).val*((1:Rat)/2)^(m+1))=
    (contourBaseRadius f hf a ha).val*((1:Rat)/2)^m
  rw [Rat.pow_succ]
  grind only

theorem nestedSquareOuter_next (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m n : Nat) :
    nestedSquareOuter f hf a ha (m+1) n ≈ nestedSquareInner f hf a ha m (n+1) := by
  have h := outerBoundary_double_inner (fixedSquareSample f hf a ha)
    (shrinkingContourRadius f hf a ha (m+1)) (2^n) (Nat.two_pow_pos n)
  rw [shrinkingContourRadius_double_next] at h
  simpa only [nestedSquareOuter,nestedSquareInner,Nat.pow_succ,Nat.mul_comm] using h

theorem nestedSquare_annulus_error (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (sub (nestedSquareInner f hf a ha m (n+1)).val
      (nestedSquareInner f hf a ha (m+1) n).val) eps.val := by
  let R := shrinkingContourRadius f hf a ha (m+1)
  let hdom := cauchyKernel_frame_domain f a R (shrinkingFrame_domain f hf a ha (m+1))
  obtain ⟨N,hN⟩ := frameContourDifference_zero (cauchyKernel f a) (cauchyKernel_holomorphic f hf a) R hdom eps
  refine ⟨N, ?_⟩
  intro n hn
  have ho : frameOuterBoundary (cauchyKernel f a) R hdom n ≈ nestedSquareInner f hf a ha m (n+1) :=
    Setoid.trans (Setoid.symm (nestedSquareOuter_actual f hf a ha (m+1) n))
      (nestedSquareOuter_next f hf a ha m n)
  have hi : frameInnerBoundary (cauchyKernel f a) R hdom n ≈ nestedSquareInner f hf a ha (m+1) n :=
    Setoid.symm (nestedSquareInner_actual f hf a ha (m+1) n)
  exact Small.congr (frameContourDifference (cauchyKernel f a) R hdom n).property
    (sub_valid (nestedSquareInner f hf a ha m (n+1)).property (nestedSquareInner f hf a ha (m+1) n).property)
    (FunctionTheory.sub_congr ho hi) (hN n hn)

def shrinkingChainError (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m n : Nat) : Scalar :=
  gridScalarSub (nestedSquareInner f hf a ha 0 (n+m)) (nestedSquareInner f hf a ha m n)

theorem shrinkingChainError_eventual (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (shrinkingChainError f hf a ha m n).val eps.val := by
  induction m generalizing eps with
  | zero =>
    refine ⟨0, ?_⟩
    intro n hn
    have hp := (nestedSquareInner f hf a ha 0 n).property
    exact Small.congr (ofQComplex_valid _) (sub_valid hp hp)
      (equiv_symm (add_neg_equiv _ hp)) (Small.zero (Rat.le_of_lt eps.property))
  | succ m ih =>
    let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
    obtain ⟨A,hA⟩ := ih eta
    obtain ⟨B,hB⟩ := nestedSquare_annulus_error f hf a ha m eta
    refine ⟨max A B, ?_⟩
    intro n hn
    have hb := LocalODE.small_add (hA (n+1) (by omega)) (hB n (by omega))
    have he : eta.val+eta.val=eps.val := by
      have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
      change 2*eta.val=eps.val at h
      grind only
    rw [he] at hb
    have hi : n+1+m=n+(m+1) := by omega
    change Small (add
      (sub (nestedSquareInner f hf a ha 0 (n+1+m)).val (nestedSquareInner f hf a ha m (n+1)).val)
      (sub (nestedSquareInner f hf a ha m (n+1)).val (nestedSquareInner f hf a ha (m+1) n).val)) eps.val at hb
    rw [hi] at hb
    exact Small.congr
      (add_valid
        (sub_valid (nestedSquareInner f hf a ha 0 (n+(m+1))).property (nestedSquareInner f hf a ha m (n+1)).property)
        (sub_valid (nestedSquareInner f hf a ha m (n+1)).property (nestedSquareInner f hf a ha (m+1) n).property))
      (shrinkingChainError f hf a ha (m+1) n).property (representedDifference_split _ _ _) hb

theorem shrinkingChainError_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (m : Nat) :
    Converges (shrinkingChainError f hf a ha m) ⟨zero,ofQComplex_valid _⟩ :=
  converge_zero _ (shrinkingChainError_eventual f hf a ha m)

end ComputableAnalysis.RiemannHilbert.RectangularContour
