import ComputableAnalysis.RiemannHilbert.RationalSeparatedSegments

/-! A constructed finite logarithm chain for every rational affine segment
with a directed-coordinate separation certificate. A terminating rational
mesh search, uniform reciprocal bound and distance estimate prove each edge
belongs to the actual logarithm chart. -/
namespace ComputableAnalysis.RiemannHilbert.RationalLogarithmMeshes
open ComplexRaw FunctionTheory LocalODE BoxApproximation NonzeroBoxSearch ReciprocalExamples LogarithmContinuation
open RationalSeparatedSegments
set_option maxHeartbeats 1000000

def displacement (p q : QComplex) : QComplex := ⟨q.re-p.re,q.im-p.im⟩
def distanceBound (p q : QComplex) : Rat := coordinateBound (displacement p q)
theorem distanceBound_nonneg (p q : QComplex) : 0 ≤ distanceBound p q := coordinateBound_nonneg _

theorem point_difference (p q : QComplex) (s t : Rat) :
    QComplex.add (point p q t) (QComplex.neg (point p q s)) = QComplex.scaleRat (t-s) (displacement p q) := by
  cases p; cases q
  simp only [point,displacement,QComplex.add,QComplex.neg,QComplex.scaleRat,QComplex.mk.injEq]
  constructor <;> grind only

theorem raw_sub_constants (p q : QComplex) : (sub (ofQComplex p) (ofQComplex q)).Equiv
    (ofQComplex (QComplex.add p (QComplex.neg q))) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).2
  apply QBox.overlaps_of_common_point (point := QComplex.add p (QComplex.neg q))
  · have hn := QBox.neg_contains (A := QBox.point q) ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    exact QBox.add_contains (QComplex.le_refl _) (QComplex.le_refl _) hn.1 hn.2
  · exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem raw_scale_constants (r : Rat) (p : QComplex) : (scaleRat r (ofQComplex p)).Equiv
    (ofQComplex (QComplex.scaleRat r p)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).2
  apply QBox.overlaps_of_common_point (point := QComplex.scaleRat r p)
  · exact QBox.scaleRat_contains (QComplex.le_refl _) (QComplex.le_refl _)
  · exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem difference_bound (p q : QComplex) (s t : Rat) (hst : 0 ≤ t-s) :
    Small (sub (rational (point p q t)).val (rational (point p q s)).val) ((t-s)*distanceBound p q) := by
  have hd := raw_sub_constants (point p q t) (point p q s)
  rw [point_difference] at hd
  have he := equiv_trans (sub_valid (rational (point p q t)).property (rational (point p q s)).property)
    (ofQComplex_valid _) (scaleRat_valid (ofQComplex_valid _)) hd (equiv_symm (raw_scale_constants (t-s) (displacement p q)))
  exact Small.congr (scaleRat_valid (ofQComplex_valid _))
    (sub_valid (rational (point p q t)).property (rational (point p q s)).property) (equiv_symm he)
    (small_scale hst (rational_small (displacement p q)))

def parameter (N i : Nat) : Rat := (i : Rat)/(N : Rat)
theorem parameter_mem (N : Nat) (hN : 0 < N) (i : Nat) (hi : i ≤ N) : UniformPath.unitInterval (parameter N i) := by
  have hn : 0 < (N : Rat) := (Rat.natCast_pos).2 hN
  have hne := Rat.ne_of_gt hn
  have hic : (i : Rat) ≤ (N : Rat) := by exact_mod_cast hi
  have hu := Rat.mul_le_mul_of_nonneg_right hic (Rat.le_of_lt ((Rat.inv_pos).2 hn))
  have he := Rat.mul_inv_cancel (N : Rat) hne
  exact ⟨Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt ((Rat.inv_pos).2 hn)),by
    change (i : Rat)*(N : Rat)⁻¹ ≤ 1
    rw [he] at hu
    exact hu⟩

theorem parameter_difference (N i : Nat) : parameter N (i+1)-parameter N i=1/(N : Rat) := by
  dsimp [parameter]
  rw [Rat.natCast_add]
  grind [Rat.div_def]

def delta (p q : QComplex) (h : Separation p q) : QPos :=
  ⟨1/(128*(inverseBound p q h+1)*(distanceBound p q+1)),by
    have hL := inverseBound_nonneg p q h
    have hW := distanceBound_nonneg p q
    exact Rat.mul_pos (by decide +kernel) ((Rat.inv_pos).2
      (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (by grind only)) (by grind only)))⟩

def count (p q : QComplex) (h : Separation p q) : Nat := UniformPath.meshStage (delta p q h)+1
theorem count_positive (p q : QComplex) (h : Separation p q) : 0 < count p q h := by unfold count; omega
theorem count_bound (p q : QComplex) (h : Separation p q) : 1/(count p q h : Rat) ≤ (delta p q h).val :=
  UniformPath.meshStage_spec (delta p q h)

theorem mesh_small (p q : QComplex) (h : Separation p q) (N : Nat) (hN : 0 < N)
    (hmesh : 1/(N : Rat) ≤ (delta p q h).val) :
    2*inverseBound p q h*((1/(N : Rat))*distanceBound p q) < LocalLogarithm.radius.val := by
  let L := inverseBound p q h
  let W := distanceBound p q
  have hL := inverseBound_nonneg p q h
  have hW := distanceBound_nonneg p q
  have heps := (delta p q h).property
  have hn : 0 ≤ 1/(N : Rat) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hN))
  have h1 := Rat.mul_le_mul_of_nonneg_left hmesh (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 2) hL) hW)
  have h2 := Rat.mul_le_mul_of_nonneg_right (show L ≤ L+1 by grind only) hW
  have h3 := Rat.mul_le_mul_of_nonneg_left (show W ≤ W+1 by grind only) (show 0 ≤ L+1 by grind only)
  have h4 := Rat.mul_le_mul_of_nonneg_right (Rat.le_trans h2 h3) (Rat.le_of_lt heps)
  have he : (delta p q h).val*(128*(L+1)*(W+1))=1 := Rat.div_mul_cancel (Rat.ne_of_gt
    (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (by grind only)) (by grind only)))
  have hr : (1/64 : Rat) < LocalLogarithm.radius.val := by decide +kernel
  change 0 ≤ L at hL
  change 0 ≤ W at hW
  change (2*L*W)*(1/(N : Rat)) ≤ (2*L*W)*(delta p q h).val at h1
  grind only

def vertex (p q : QComplex) (N i : Nat) : Scalar := rational (point p q (parameter N i))
theorem vertex_nonzero (p q : QComplex) (h : Separation p q) (N : Nat) (hN : 0 < N) (i : Nat) (hi : i ≤ N) :
    Nonzero (vertex p q N i) := rational_nonzero _ (normSq_ne_zero p q h _ (parameter_mem N hN i hi))

theorem edge_mem (p q : QComplex) (h : Separation p q) (N : Nat) (hN : 0 < N)
    (hmesh : 1/(N : Rat) ≤ (delta p q h).val) (i : Nat) (hi : i+1 ≤ N) :
    RelativeLogarithm.domain (vertex p q N i) (vertex_nonzero p q h N hN i (by omega)) (vertex p q N (i+1)) := by
  let L := inverseBound p q h
  let H := (1/(N : Rat))*distanceBound p q
  have hL := inverseBound_nonneg p q h
  have hNrat : 0 ≤ 1/(N : Rat) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hN))
  have hH : 0 ≤ H := Rat.mul_nonneg hNrat (distanceBound_nonneg p q)
  have hInv : Small (RepresentedReciprocal.inverse (vertex p q N i) (vertex_nonzero p q h N hN i (by omega))).val L := by
    have hb := (rational_small (RationalReciprocal.inverse (point p q (parameter N i)))).mono
      (inverse_bound p q h _ (parameter_mem N hN i (by omega)))
    exact Small.congr (ofQComplex_valid _) (RepresentedReciprocal.inverse _ _).property
      (equiv_symm (rational_inverse _ (normSq_ne_zero p q h _ (parameter_mem N hN i (by omega))))) hb
  have hd := difference_bound p q (parameter N i) (parameter N (i+1)) (by rw [parameter_difference]; exact hNrat)
  rw [parameter_difference] at hd
  exact RelativeLogarithm.domain_of_distance _ _ _ L H hL hH hInv hd (mesh_small p q h N hN hmesh)

def fromNode (p q : QComplex) (h : Separation p q) (N : Nat) (hN : 0 < N)
    (hmesh : 1/(N : Rat) ≤ (delta p q h).val) : (i k : Nat) → (hik : i+k=N) →
    Chain (vertex p q N i) (vertex_nonzero p q h N hN i (by omega))
      (vertex p q N N) (vertex_nonzero p q h N hN N (Nat.le_refl N))
  | i,0,hik => by
      have hi : i=N := by omega
      subst i
      exact .nil _ _
  | i,k+1,hik => .step (edge_mem p q h N hN hmesh i (by omega)) (fromNode p q h N hN hmesh (i+1) k (by omega))

theorem left_normSq_ne_zero (p q : QComplex) (h : Separation p q) : QComplex.normSq p ≠ 0 := by
  have hn := normSq_ne_zero p q h 0 ⟨by decide +kernel,by decide +kernel⟩
  rw [point_zero] at hn
  exact hn
theorem right_normSq_ne_zero (p q : QComplex) (h : Separation p q) : QComplex.normSq q ≠ 0 := by
  have hn := normSq_ne_zero p q h 1 ⟨by decide +kernel,by decide +kernel⟩
  rw [point_one] at hn
  exact hn

theorem vertex_zero (p q : QComplex) (N : Nat) : vertex p q N 0=rational p := by
  change rational (point p q (0/(N : Rat)))=rational p
  rw [Rat.div_def,Rat.zero_mul,point_zero]
theorem vertex_last (p q : QComplex) (N : Nat) (hN : 0 < N) : vertex p q N N=rational q := by
  have he := Rat.mul_inv_cancel (N : Rat) (Rat.ne_of_gt ((Rat.natCast_pos).2 hN))
  simp only [vertex,parameter,Rat.div_def,he,point_one]

def changeEndpoints {c d c' d' : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    {hc' : Nonzero c'} {hd' : Nonzero d'} (hl : c=c') (hr : d=d') (p : Chain c hc d hd) : Chain c' hc' d' hd' := by
  subst c'
  subst d'
  exact p

def chain (p q : QComplex) (h : Separation p q) :
    Chain (rational p) (rational_nonzero p (left_normSq_ne_zero p q h))
      (rational q) (rational_nonzero q (right_normSq_ne_zero p q h)) :=
  changeEndpoints (vertex_zero p q (count p q h)) (vertex_last p q (count p q h) (count_positive p q h))
    (fromNode p q h (count p q h) (count_positive p q h) (count_bound p q h) 0 (count p q h) (by omega))

end ComputableAnalysis.RiemannHilbert.RationalLogarithmMeshes
