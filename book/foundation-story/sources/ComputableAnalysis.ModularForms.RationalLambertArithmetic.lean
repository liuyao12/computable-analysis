import ComputableAnalysis.ModularForms.WeightedLambertSeries
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Exact finite rational Lambert arithmetic, compared with the certified
geometric-series factors. No represented reciprocal is executed in a sample. -/
namespace ComputableAnalysis.ModularForms.RationalLambert
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 1000000

abbrev point (q : QComplex) : Scalar := ⟨ofQComplex q,ofQComplex_valid q⟩

theorem add_constants (p q : QComplex) :
    (add (ofQComplex p) (ofQComplex q)).Equiv (ofQComplex (QComplex.add p q)) := by
  intro k
  exact (compareAt_overlap_iff _ _ k k).mpr (QBox.overlaps_of_common_point
    (QBox.add_contains (QComplex.le_refl _) (QComplex.le_refl _) (QComplex.le_refl _) (QComplex.le_refl _))
    ⟨QComplex.le_refl _,QComplex.le_refl _⟩)

theorem sub_constants (p q : QComplex) :
    (sub (ofQComplex p) (ofQComplex q)).Equiv (ofQComplex (QComplex.sub p q)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).mpr
  apply QBox.overlaps_of_common_point (point := QComplex.sub p q)
  · have hn := QBox.neg_contains (A := QBox.point q) ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    exact QBox.add_contains (QComplex.le_refl _) (QComplex.le_refl _) hn.1 hn.2
  · exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem scale_constants (r : Rat) (p : QComplex) :
    (scaleRat r (ofQComplex p)).Equiv (ofQComplex (QComplex.scaleRat r p)) := by
  intro k
  exact (compareAt_overlap_iff _ _ k k).mpr (QBox.overlaps_of_common_point
    (QBox.scaleRat_contains (QComplex.le_refl _) (QComplex.le_refl _))
    ⟨QComplex.le_refl _,QComplex.le_refl _⟩)

theorem power_constants (q : QComplex) (n : Nat) :
    (LocalODE.power (ofQComplex q) n).Equiv (ofQComplex (QComplex.natPow q n)) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih =>
    exact equiv_trans (LocalODE.power_valid _ (ofQComplex_valid _) (n+1))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (mul_equiv (LocalODE.power_valid _ (ofQComplex_valid _) n) (ofQComplex_valid _)
        (ofQComplex_valid _) (ofQComplex_valid _) ih (equiv_refl _ (ofQComplex_valid _)))
      (RationalReciprocal.raw_mul_constants _ _)

def denominator (q : QComplex) (n : Nat) : QComplex := QComplex.sub QComplex.one (QComplex.natPow q (n+1))
def factor (q : QComplex) (n : Nat) : QComplex :=
  QComplex.mul (QComplex.natPow q (n+1)) (RationalReciprocal.inverse (denominator q n))

theorem denominator_agrees (q : QComplex) (n : Nat) :
    (sub one (LocalODE.power (ofQComplex q) (n+1))).Equiv (ofQComplex (denominator q n)) :=
  equiv_trans (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ (ofQComplex_valid _) _))
    (sub_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (FunctionTheory.sub_congr (equiv_refl _ (ofQComplex_valid _)) (power_constants q (n+1)))
    (sub_constants _ _)

theorem denominator_nonzero (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64)) (n : Nat) :
    QComplex.normSq (denominator q n) ≠ 0 := by
  let p := nomePowerScalar (point q) n
  let r := nomePowerRadius (1/64) n
  let d : Scalar := ⟨sub one p.val,sub_valid (ofQComplex_valid _) p.property⟩
  let s : Scalar := ⟨nomeGeometricSum p r,nomeGeometricSum_valid p r
    (nomePowerRadius_nonneg _ (by decide +kernel) n) (nomePowerRadius_local (1/64) (by decide +kernel) (by decide +kernel) n)
    (nomePowerScalar_small (point q) (1/64) (by decide +kernel) hq n)⟩
  have hn := RepresentedReciprocal.nonzero_of_inverse d s (nomeGeometricSum_inverse p r
    (nomePowerRadius_nonneg _ (by decide +kernel) n) (nomePowerRadius_local (1/64) (by decide +kernel) (by decide +kernel) n)
    (nomePowerScalar_small (point q) (1/64) (by decide +kernel) hq n))
  intro hzero
  have he := denominator_agrees q n
  rw [QComplex.normSq_eq_zero_iff.mp hzero] at he
  exact hn he

theorem geometric_agrees (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64)) (n : Nat) :
    (nomeGeometricSum (nomePowerScalar (point q) n) (nomePowerRadius (1/64) n)).Equiv
      (ofQComplex (RationalReciprocal.inverse (denominator q n))) := by
  let p := nomePowerScalar (point q) n
  let r := nomePowerRadius (1/64) n
  let d : Scalar := ⟨sub one p.val,sub_valid (ofQComplex_valid _) p.property⟩
  let s : Scalar := ⟨nomeGeometricSum p r,nomeGeometricSum_valid p r
    (nomePowerRadius_nonneg _ (by decide +kernel) n) (nomePowerRadius_local (1/64) (by decide +kernel) (by decide +kernel) n)
    (nomePowerScalar_small (point q) (1/64) (by decide +kernel) hq n)⟩
  apply RepresentedReciprocal.unique d s (point (RationalReciprocal.inverse (denominator q n)))
  · exact nomeGeometricSum_inverse p r (nomePowerRadius_nonneg _ (by decide +kernel) n)
      (nomePowerRadius_local (1/64) (by decide +kernel) (by decide +kernel) n) (nomePowerScalar_small (point q) (1/64) (by decide +kernel) hq n)
  · have hp := RationalReciprocal.raw_mul_constants (denominator q n) (RationalReciprocal.inverse (denominator q n))
    rw [RationalReciprocal.mul_inverse _ (denominator_nonzero q hq n)] at hp
    exact equiv_trans (mul_valid d.property (ofQComplex_valid _))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (mul_equiv d.property (ofQComplex_valid _) (ofQComplex_valid _) (ofQComplex_valid _)
        (denominator_agrees q n) (equiv_refl _ (ofQComplex_valid _))) hp

def term (q : QComplex) (k n : Nat) : QComplex := QComplex.scaleRat (((n+1:Nat):Rat)^k) (factor q n)
def finitePrefix (q : QComplex) (k : Nat) : Nat → QComplex
  | 0 => QComplex.zero
  | n+1 => QComplex.add (finitePrefix q k n) (term q k n)

theorem term_agrees (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64)) (k n : Nat) :
    (weightedLambertTerm (point q) (1/64) k n).Equiv (ofQComplex (term q k n)) := by
  have hf : (nomeLambertPower (point q) (1/64) n).Equiv (ofQComplex (factor q n)) := equiv_trans (nomeLambertPower_valid (point q) (1/64) (by decide +kernel) (by decide +kernel) hq n)
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (mul_equiv (nomePowerScalar (point q) n).property (ofQComplex_valid _)
      (nomeGeometricSum_valid (nomePowerScalar (point q) n) (nomePowerRadius (1/64) n) (nomePowerRadius_nonneg (1/64) (by decide +kernel) n)
        (nomePowerRadius_local (1/64) (by decide +kernel) (by decide +kernel) n) (nomePowerScalar_small (point q) (1/64) (by decide +kernel) hq n))
      (ofQComplex_valid _) (power_constants q (n+1)) (geometric_agrees q hq n))
    (RationalReciprocal.raw_mul_constants _ _)
  exact equiv_trans (weightedLambertTerm_valid (point q) (1/64) k (by decide +kernel) (by decide +kernel) hq n)
    (scaleRat_valid (ofQComplex_valid _)) (ofQComplex_valid _) (scaleRat_equiv hf) (scale_constants _ _)

theorem prefix_agrees (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64)) (k N : Nat) :
    (ScalarSeries.block (weightedLambertTerm (point q) (1/64) k) 0 N).Equiv (ofQComplex (finitePrefix q k N)) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    simp only [ScalarSeries.block.eq_2,Nat.zero_add]
    change (add (ScalarSeries.block (weightedLambertTerm (point q) (1/64) k) 0 N)
      (weightedLambertTerm (point q) (1/64) k N)).Equiv (ofQComplex (finitePrefix q k (N+1)))
    exact equiv_trans (add_valid (ScalarSeries.block_valid (weightedLambertTerm (point q) (1/64) k)
      (weightedLambertTerm_valid (point q) (1/64) k (by decide +kernel) (by decide +kernel) hq) 0 N)
      (weightedLambertTerm_valid (point q) (1/64) k (by decide +kernel) (by decide +kernel) hq N))
      (add_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (add_equiv ih (term_agrees q hq k N)) (add_constants _ _)

end ComputableAnalysis.ModularForms.RationalLambert
