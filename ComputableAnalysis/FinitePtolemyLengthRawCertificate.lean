import ComputableAnalysis.RationalCircle

/-!
# A raw-length Ptolemy certificate

This is the unsigned-length bridge for the rational-circle Ptolemy identity.
Lengths are represented by the project's computable square-root algorithm; no
standard real numbers or infinitary geometric object is imported.
-/

namespace ComputableAnalysis
namespace FinitePtolemyLengthRaw

open RationalCircle
open RationalCircle.Stage

private theorem rat_sq_nonneg (x : Rat) : 0 <= sq x := by
  unfold sq
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    simpa [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg] using hsq

def chordNormSq (p q : PiCirclePoint) : Rat :=
  segmentNormSq p q

def chordLengthRaw (p q : PiCirclePoint) : RealRaw :=
  sqrtRaw (chordNormSq p q) (by
    unfold sqrtDomain chordNormSq segmentNormSq
    have hx := rat_sq_nonneg (q.x - p.x)
    have hy := rat_sq_nonneg (q.y - p.y)
    grind [sq])

theorem chordLengthRaw_equiv_of_square
    (p q : PiCirclePoint) (r : Rat)
    (hsquare : sq r = chordNormSq p q) :
    (chordLengthRaw p q).Equiv (RealRaw.ofRat (qabs r)) := by
  let hq : sqrtDomain (chordNormSq p q) := by
    unfold sqrtDomain
    rw [← hsquare]
    have hr := rat_sq_nonneg r
    grind
  have hspec := sqrtRaw_spec (chordNormSq p q) hq
  have hreal := sqrt_rational_of_square
    (chordNormSq p q) r hq hspec hsquare
  simpa [chordLengthRaw, sqrtReal, Real.ofRat, Real.ofRaw, Real.Equiv] using hreal

structure LengthWitnessCertificate where
  a : PiCirclePoint
  b : PiCirclePoint
  c : PiCirclePoint
  d : PiCirclePoint
  ab : Rat
  bc : Rat
  cd : Rat
  da : Rat
  ac : Rat
  bd : Rat
  hab : sq ab = chordNormSq a b
  hbc : sq bc = chordNormSq b c
  hcd : sq cd = chordNormSq c d
  hda : sq da = chordNormSq d a
  hac : sq ac = chordNormSq a c
  hbd : sq bd = chordNormSq b d
  nonneg : 0 ≤ ab ∧ 0 ≤ bc ∧ 0 ≤ cd ∧ 0 ≤ da ∧ 0 ≤ ac ∧ 0 ≤ bd
  ptolemy : ac * bd = ab * cd + bc * da

theorem LengthWitnessCertificate.raw_lengths_and_ptolemy
    (w : LengthWitnessCertificate) :
    (chordLengthRaw w.a w.b).Equiv (RealRaw.ofRat w.ab) ∧
      (chordLengthRaw w.b w.c).Equiv (RealRaw.ofRat w.bc) ∧
      (chordLengthRaw w.c w.d).Equiv (RealRaw.ofRat w.cd) ∧
      (chordLengthRaw w.d w.a).Equiv (RealRaw.ofRat w.da) ∧
      (chordLengthRaw w.a w.c).Equiv (RealRaw.ofRat w.ac) ∧
      (chordLengthRaw w.b w.d).Equiv (RealRaw.ofRat w.bd) ∧
      w.ac * w.bd = w.ab * w.cd + w.bc * w.da := by
  rcases w with ⟨a, b, c, d, ab, bc, cd, da, ac, bd,
    hab, hbc, hcd, hda, hac, hbd, hn, hp⟩
  rcases hn with ⟨hab0, hbc0, hcd0, hda0, hac0, hbd0⟩
  have eab := chordLengthRaw_equiv_of_square a b ab hab
  have ebc := chordLengthRaw_equiv_of_square b c bc hbc
  have ecd := chordLengthRaw_equiv_of_square c d cd hcd
  have eda := chordLengthRaw_equiv_of_square d a da hda
  have eac := chordLengthRaw_equiv_of_square a c ac hac
  have ebd := chordLengthRaw_equiv_of_square b d bd hbd
  simp only [qabs_eq_self_of_nonneg hab0, qabs_eq_self_of_nonneg hbc0,
    qabs_eq_self_of_nonneg hcd0, qabs_eq_self_of_nonneg hda0,
    qabs_eq_self_of_nonneg hac0, qabs_eq_self_of_nonneg hbd0] at eab ebc ecd eda eac ebd
  exact ⟨eab, ebc, ecd, eda, eac, ebd, hp⟩

def ptolemyLengthWitness : LengthWitnessCertificate where
  a := point 0
  b := point (8 / 15)
  c := point (3 / 4)
  d := point (4 / 3)
  ab := 16 / 17
  bc := 26 / 85
  cd := 14 / 25
  da := 8 / 5
  ac := 6 / 5
  bd := 72 / 85
  hab := by dsimp [chordNormSq]; rw [point_segmentNormSq_formula]; native_decide
  hbc := by dsimp [chordNormSq]; rw [point_segmentNormSq_formula]; native_decide
  hcd := by dsimp [chordNormSq]; rw [point_segmentNormSq_formula]; native_decide
  hda := by dsimp [chordNormSq]; rw [point_segmentNormSq_formula]; native_decide
  hac := by dsimp [chordNormSq]; rw [point_segmentNormSq_formula]; native_decide
  hbd := by dsimp [chordNormSq]; rw [point_segmentNormSq_formula]; native_decide
  nonneg := by native_decide
  ptolemy := by native_decide

theorem ptolemyLengthWitness_raw_lengths_and_ptolemy :
    (chordLengthRaw (point 0) (point (8 / 15))).Equiv
        (RealRaw.ofRat (16 / 17)) ∧
      (chordLengthRaw (point (8 / 15)) (point (3 / 4))).Equiv
        (RealRaw.ofRat (26 / 85)) ∧
      (chordLengthRaw (point (3 / 4)) (point (4 / 3))).Equiv
        (RealRaw.ofRat (14 / 25)) ∧
      (chordLengthRaw (point (4 / 3)) (point 0)).Equiv
        (RealRaw.ofRat (8 / 5)) ∧
      (chordLengthRaw (point 0) (point (3 / 4))).Equiv
        (RealRaw.ofRat (6 / 5)) ∧
      (chordLengthRaw (point (8 / 15)) (point (4 / 3))).Equiv
        (RealRaw.ofRat (72 / 85)) ∧
      (6 / 5 : Rat) * (72 / 85) =
        (16 / 17) * (14 / 25) + (26 / 85) * (8 / 5) := by
  simpa [ptolemyLengthWitness] using
    LengthWitnessCertificate.raw_lengths_and_ptolemy ptolemyLengthWitness

end FinitePtolemyLengthRaw
end ComputableAnalysis
