import ComputableAnalysis.ModularForms.DiskLambertPolynomials
import ComputableAnalysis.ModularForms.EisensteinDiskPatches

/-! Actual represented-input bridges for the finite polynomial certificates.
Continuity of each finite polynomial and the existing rational-sample lift
transfer the uniform rational estimates to every point of a compact patch. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions RationalLambert CauchyTaylor
open EisensteinDiskPatches
set_option maxHeartbeats 1000000

theorem select_sample (P : Patch) (q : Scalar) (hq : EisensteinDiskPatches.domain P q)
    (hd : EisensteinUnitDisk.domain q) (k : Nat) (F : DomainFunctions.Map)
    (hD : ∀z, F.domain z) (hF : ContinuousOn F.domain F.eval) (eps : QPos) :
    ∃T, InDisk (samplePoint q hd k T) (EisensteinDiskPatches.radius P) ∧
      (RepresentedCauchySum.error T).val≤eps.val ∧
      Small (sub (F.eval (point (samplePoint q hd k T)) (hD _)).val (F.eval q (hD q)).val) eps.val := by
  let eta := minRadius eps (hF.delta q (hD q) eps)
  obtain ⟨A,hA⟩ := samples_eventually_inside P q hq hd k
  obtain ⟨B,hB⟩ := RepresentedCauchySum.error_shrinks eta
  let T := max A B
  have herr := hB T (Nat.le_max_right A B)
  have hs := (sample_close q hd k T).mono (Rat.le_trans (inputRadius_le_error q hd k T)
    (Rat.le_trans herr (minRadius_right _ _)))
  exact ⟨T,hA T (Nat.le_max_left A B),Rat.le_trans herr (minRadius_left _ _),hF.estimate q (hD q) eps _ (hD _) hs⟩

theorem polynomial_patch_bound (P : Patch) (q : Scalar) (hq : EisensteinDiskPatches.domain P q) (k M N : Nat) :
    Small ((polynomialMap k M N).eval q trivial).val (2*budget (EisensteinDiskPatches.radius P) k) := by
  apply SeriesLimitLaws.small_closed _ _ (fun j => (RepresentedCauchySum.error j).val) RepresentedCauchySum.error_shrinks
  intro j
  obtain ⟨T,hT,_,hF⟩ := select_sample P q hq (included P q hq) k (polynomialMap k M N)
    (fun _ => trivial) (polynomialMap_holomorphic k M N).continuous (RepresentedCauchySum.error j)
  let p := samplePoint q (included P q hq) k T
  have hb := rational_norm_small _ _ (polynomialPrefix_bound p _ (Rat.le_of_lt (radius_pos P)) (radius_lt_one P) hT k M N)
  have hbp := Small.congr (ofQComplex_valid _) ((polynomialMap k M N).eval (point p) trivial).property
    (equiv_symm (polynomialMap_rational p k M N)) hb
  have hs := LocalODE.small_add hbp (RepresentedCauchySum.small_sub_symm _ _ _ hF)
  exact Small.congr (add_valid ((polynomialMap k M N).eval (point p) trivial).property
    (sub_valid ((polynomialMap k M N).eval q trivial).property ((polynomialMap k M N).eval (point p) trivial).property))
    ((polynomialMap k M N).eval q trivial).property
    (SeriesLimitLaws.add_difference _ _ ((polynomialMap k M N).eval q trivial).property
      ((polynomialMap k M N).eval (point p) trivial).property) hs

theorem value_polynomial_close (P : Patch) (q : Scalar) (hq : EisensteinDiskPatches.domain P q) (k N : Nat) :
    Small (sub (value q (included P q hq) k)
      ((polynomialMap k N (cutoff (EisensteinDiskPatches.radius P) k+N)).eval q trivial).val)
      (polynomialError (EisensteinDiskPatches.radius P) k N) := by
  let r := EisensteinDiskPatches.radius P
  let F := polynomialMap k N (cutoff r k+N)
  apply SeriesLimitLaws.small_closed _ _ (fun j => 3*(RepresentedCauchySum.error j).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks 3 (by decide +kernel))
  intro j
  obtain ⟨T,hT,herr,hF⟩ := select_sample P q hq (included P q hq) k F (fun _ => trivial)
    (polynomialMap_holomorphic k N (cutoff r k+N)).continuous (RepresentedCauchySum.error j)
  let p := samplePoint q (included P q hq) k T
  have h1 := (value_close_sample q (included P q hq) k T).mono
    (Rat.mul_le_mul_of_nonneg_left herr (by decide +kernel : (0:Rat)≤2))
  have h2 := rational_polynomial_close p r (Rat.le_of_lt (radius_pos P)) (radius_lt_one P) hT k N
  have h2' := Small.congr (sub_valid (rationalValue_valid p (sample_unit_disk q (included P q hq) k T) k) (ofQComplex_valid _))
    (sub_valid (rationalValue_valid p (sample_unit_disk q (included P q hq) k T) k) (F.eval (point p) trivial).property)
    (FunctionTheory.sub_congr (equiv_refl _ (rationalValue_valid p (sample_unit_disk q (included P q hq) k T) k))
      (equiv_symm (polynomialMap_rational p k N (cutoff r k+N)))) h2
  have h12 := triangle _ _ _ (value_valid q (included P q hq) k)
    (rationalValue_valid p (sample_unit_disk q (included P q hq) k T) k) (F.eval (point p) trivial).property _ _ h1 h2'
  have h123 := triangle _ _ _ (value_valid q (included P q hq) k) (F.eval (point p) trivial).property
    (F.eval q trivial).property _ _ h12 hF
  exact h123.mono (by grind only)
end ComputableAnalysis.ModularForms.DiskLambert
