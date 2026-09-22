import ComputableAnalysis.QuadratureCertificate
import ComputableAnalysis.RationalLipschitzIntegral

/-!
# Semantic certificates for existing quadrature programs

These adapters leave the numerical programs and their validity proofs intact.
They add the finite spatial meaning required by `Quadrature.Certificate`.
-/
namespace ComputableAnalysis.Quadrature
open ClosedArctanInverse MonotoneAverage RationalSampleLimits TaggedQuadrature

/-- The existing rational-Lipschitz construction controls all rational tags,
not just the left samples used by its runtime. -/
def ofRationalLipschitz (D : RationalLipschitzIntegral.Data) :
    Certificate (fun x => RealRaw.ofRat (D.sample x)) 0 1 (RationalLipschitzIntegral.raw D) where
  ordered := by decide
  function_valid := fun _ _ _ => RealRaw.ofRat_valid _
  value_valid := RationalLipschitzIntegral.valid D
  sample := fun x _ => D.sample x
  sample_mem := fun _ _ _ _ => ⟨Rat.le_refl,Rat.le_refl⟩
  output := RationalLipschitzIntegral.centre D
  output_mem := fun q => RationalLipschitzIntegral.contains_future D q q (Nat.le_refl q)
  error := 2*(D.constant:Rat)
  error_nonneg := Rat.mul_nonneg (by decide) Rat.natCast_nonneg
  estimate := by
    intro d tag eps
    refine ⟨d,fun q hdq => ?_⟩
    have hm := RationalLipschitzIntegral.mesh_error D.sample D.constant Rat.natCast_nonneg D.bound d q hdq
    have ht := lipschitz_tag_error D.sample D.constant Rat.natCast_nonneg D.bound tag
      (a:=0) (b:=1) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide) d
    have hh := qabs_sub_le
      (left D.sample 0 1 q-left D.sample 0 1 d)
      (average D.sample tag 0 1 d-left D.sample 0 1 d)
    have he : (left D.sample 0 1 q-left D.sample 0 1 d)-
      (average D.sample tag 0 1 d-left D.sample 0 1 d)=
      left D.sample 0 1 q-average D.sample tag 0 1 d := by grind only
    rw [he] at hh
    simp only [show (1:Rat)-0=1 by decide +kernel,Rat.mul_one] at ht
    change qabs (left D.sample 0 1 q-(1-0)*average D.sample tag 0 1 d) ≤ _
    simp only [show (1:Rat)-0=1 by decide +kernel,Rat.one_mul]
    have hp:=eps.property
    grind only

/-- Computable-valued monotone samples retain their own independent pointwise
raw representatives. Fixed-grid evaluation precision is not identified with
the spatial mesh in the meaning certificate. -/
def ofMonotoneSamples (D : MonotoneSampleIntegral.Data) (f : Rat → RealRaw)
    (hf : ∀ x, Unit x → (f x).Valid)
    (hs : ∀ x q, Unit x → IntervalSelections.InBox (D.sample x q) ((f x).compute q)) :
    Certificate f 0 1 (MonotoneSampleIntegral.raw D) where
  ordered := by decide
  function_valid := fun x hx hy => hf x ⟨hx,hy⟩
  value_valid := MonotoneSampleIntegral.valid D
  sample := D.sample
  sample_mem := fun x q hx hy => hs x q ⟨hx,hy⟩
  output := MonotoneSampleIntegral.centre D
  output_mem := fun q => MonotoneSampleIntegral.contains_future D q q (Nat.le_refl q)
  error := 2
  error_nonneg := by decide
  estimate := by
    intro d tag eps
    refine ⟨d,fun q hdq => ?_⟩
    have hb0 := D.bound 0 q ⟨by decide,by decide⟩
    have hb1 := D.bound 1 q ⟨by decide,by decide⟩
    have hm := MonotoneAverage.mesh_error (fun x => D.sample x q) (D.decreasing q) hb1.1 hb0.2 hdq
    have ht := decreasing_bounds (fun x => D.sample x q) (D.decreasing q) tag
      (a:=0) (b:=1) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide) d
    have hg := gap (fun x => D.sample x q) 0 1 d
    have he := Rat.mul_le_mul_of_nonneg_left (show D.sample 0 q-D.sample 1 q≤1 by grind only)
      (Rat.le_of_lt (meshRadius_pos d))
    have tagbound : qabs (average (fun x => D.sample x q) tag 0 1 d-left (fun x => D.sample x q) 0 1 d)≤meshRadius d := by
      rw [qabs_eq_neg_of_nonpos (by grind only)]
      grind only
    have hh := qabs_add_le
      (left (fun x => D.sample x q) 0 1 d-left (fun x => D.sample x q) 0 1 q)
      (average (fun x => D.sample x q) tag 0 1 d-left (fun x => D.sample x q) 0 1 d)
    have hid : (left (fun x => D.sample x q) 0 1 d-left (fun x => D.sample x q) 0 1 q)+
      (average (fun x => D.sample x q) tag 0 1 d-left (fun x => D.sample x q) 0 1 d)=
      -(left (fun x => D.sample x q) 0 1 q-average (fun x => D.sample x q) tag 0 1 d) := by grind only
    rw [hid,qabs_neg] at hh
    change qabs (left (fun x => D.sample x q) 0 1 q-(1-0)*average (fun x => D.sample x q) tag 0 1 d)≤_
    simp only [show (1:Rat)-0=1 by decide +kernel,Rat.one_mul]
    have hp:=eps.property
    grind only

/-- The existing Lipschitz evaluator packaged with its retained semantic
certificate for the domain-aware public function. -/
def rationalLipschitzFor (D : RationalLipschitzIntegral.Data) :
    ConstructionFor (FunctionOnInterval.exactRat D.sample 0 1) where
  value := RationalLipschitzIntegral.raw D
  meaning := (ofRationalLipschitz D).congr_function
    (fun x _ _ => intervalRaw_valid _ x) (by
      intro x hx hy
      have hdom : (FunctionOnInterval.exactRat D.sample 0 1).lower ≤ x ∧
          x ≤ (FunctionOnInterval.exactRat D.sample 0 1).upper := ⟨hx,hy⟩
      unfold intervalRaw
      rw [dif_pos hdom]
      exact RealRaw.equiv_refl _ (RealRaw.ofRat_valid _))

end ComputableAnalysis.Quadrature
