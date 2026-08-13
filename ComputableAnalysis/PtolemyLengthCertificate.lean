import ComputableAnalysis.FinitePtolemyLength

/-!
# Reusable finite Ptolemy length interface

The classical theorem is not assumed here.  A finite certificate supplies
the six rational squared chord values, nonnegative rational length witnesses,
and the final rational Ptolemy equality.  The existing square-root bridge
then lifts all six witnesses to the project's `RealRaw` length algorithms.
-/

namespace ComputableAnalysis

namespace FinitePtolemyLength

structure LengthWitnessCertificate where
  a b c d : PiCirclePoint
  ab bc cd da ac bd : Rat
  hab : sq ab = pointSegmentNormSq a b
  hbc : sq bc = pointSegmentNormSq b c
  hcd : sq cd = pointSegmentNormSq c d
  hda : sq da = pointSegmentNormSq d a
  hac : sq ac = pointSegmentNormSq a c
  hbd : sq bd = pointSegmentNormSq b d
  hab_nonneg : 0 <= ab
  hbc_nonneg : 0 <= bc
  hcd_nonneg : 0 <= cd
  hda_nonneg : 0 <= da
  hac_nonneg : 0 <= ac
  hbd_nonneg : 0 <= bd
  ptolemy : ab * cd + bc * da = ac * bd

theorem LengthWitnessCertificate.raw_lengths_and_ptolemy
    (certificate : LengthWitnessCertificate) :
    (pointSegmentLengthRaw certificate.a certificate.b).Equiv
        (RealRaw.ofRat certificate.ab) /\
      (pointSegmentLengthRaw certificate.b certificate.c).Equiv
        (RealRaw.ofRat certificate.bc) /\
      (pointSegmentLengthRaw certificate.c certificate.d).Equiv
        (RealRaw.ofRat certificate.cd) /\
      (pointSegmentLengthRaw certificate.d certificate.a).Equiv
        (RealRaw.ofRat certificate.da) /\
      (pointSegmentLengthRaw certificate.a certificate.c).Equiv
        (RealRaw.ofRat certificate.ac) /\
      (pointSegmentLengthRaw certificate.b certificate.d).Equiv
        (RealRaw.ofRat certificate.bd) /\
      certificate.ab * certificate.cd + certificate.bc * certificate.da =
        certificate.ac * certificate.bd := by
  have hab := pointSegmentLengthRaw_equiv_of_square
    certificate.a certificate.b certificate.ab certificate.hab
  have hbc := pointSegmentLengthRaw_equiv_of_square
    certificate.b certificate.c certificate.bc certificate.hbc
  have hcd := pointSegmentLengthRaw_equiv_of_square
    certificate.c certificate.d certificate.cd certificate.hcd
  have hda := pointSegmentLengthRaw_equiv_of_square
    certificate.d certificate.a certificate.da certificate.hda
  have hac := pointSegmentLengthRaw_equiv_of_square
    certificate.a certificate.c certificate.ac certificate.hac
  have hbd := pointSegmentLengthRaw_equiv_of_square
    certificate.b certificate.d certificate.bd certificate.hbd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, certificate.ptolemy⟩
  · simpa [qabs_eq_self_of_nonneg certificate.hab_nonneg] using hab
  · simpa [qabs_eq_self_of_nonneg certificate.hbc_nonneg] using hbc
  · simpa [qabs_eq_self_of_nonneg certificate.hcd_nonneg] using hcd
  · simpa [qabs_eq_self_of_nonneg certificate.hda_nonneg] using hda
  · simpa [qabs_eq_self_of_nonneg certificate.hac_nonneg] using hac
  · simpa [qabs_eq_self_of_nonneg certificate.hbd_nonneg] using hbd

def ptolemyLengthWitness : LengthWitnessCertificate where
  a := ptolemyPointA
  b := ptolemyPointB
  c := ptolemyPointC
  d := ptolemyPointD
  ab := 16 / 17
  bc := 26 / 85
  cd := 14 / 25
  da := 8 / 5
  ac := 6 / 5
  bd := 72 / 85
  hab := by
    have h := ptolemyPoint_square_coordinates
    rw [h.1]
    native_decide
  hbc := by
    have h := ptolemyPoint_square_coordinates
    rw [h.2.1]
    native_decide
  hcd := by
    have h := ptolemyPoint_square_coordinates
    rw [h.2.2.1]
    native_decide
  hda := by
    have h := ptolemyPoint_square_coordinates
    rw [h.2.2.2.1]
    native_decide
  hac := by
    have h := ptolemyPoint_square_coordinates
    rw [h.2.2.2.2.1]
    native_decide
  hbd := by
    have h := ptolemyPoint_square_coordinates
    rw [h.2.2.2.2.2]
    native_decide
  hab_nonneg := by native_decide
  hbc_nonneg := by native_decide
  hcd_nonneg := by native_decide
  hda_nonneg := by native_decide
  hac_nonneg := by native_decide
  hbd_nonneg := by native_decide
  ptolemy := by native_decide

theorem ptolemyLengthWitness_raw_lengths_and_ptolemy :
    ptolemyLengthWitness.raw_lengths_and_ptolemy := by
  exact LengthWitnessCertificate.raw_lengths_and_ptolemy ptolemyLengthWitness

end FinitePtolemyLength

end ComputableAnalysis
