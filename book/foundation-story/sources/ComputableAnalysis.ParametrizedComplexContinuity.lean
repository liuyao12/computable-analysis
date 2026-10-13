import ComputableAnalysis.ParametrizedLimits
import ComputableAnalysis.Holomorphic
import ComputableAnalysis.RiemannHilbert.DomainFunctions
import ComputableAnalysis.RiemannHilbert.LocalODEMajorant

/-! Existing complex continuity moduli imply the same covered valid-diagonal
specification in each coordinate. Every complex direction is covered. -/
namespace ComputableAnalysis.FunctionTheory
open RawLimit ComplexRaw
set_option maxHeartbeats 2000000

/-- Finite running minima give nested domain-relative neighborhoods while
retaining the actual supplied local moduli as executable data. -/
def runningRadius (delta : Nat → QPos) : Nat → QPos
  | 0 => delta 0
  | n+1 => ⟨min (runningRadius delta n).val (delta (n+1)).val,by
      have a := (runningRadius delta n).property
      have b := (delta (n+1)).property
      grind⟩

theorem runningRadius_le (delta : Nat → QPos) (n : Nat) :
    (runningRadius delta n).val ≤ (delta n).val := by
  cases n with
  | zero => exact Rat.le_refl
  | succ n => dsimp [runningRadius]; grind

theorem runningRadius_antitone (delta : Nat → QPos) :
    ∀ i j, i ≤ j → (runningRadius delta j).val ≤ (runningRadius delta i).val := by
  intro i j hij
  induction hij with
  | refl => exact Rat.le_refl
  | @step j hij ih =>
    have h : (runningRadius delta (j+1)).val ≤ (runningRadius delta j).val := by
      dsimp [runningRadius]; grind
    exact Rat.le_trans h ih

theorem small_sub_coordinate_enclosures {z c : ComplexRaw} (hz : z.Valid) (hc : c.Valid)
    {eps : Rat} (h : Small (sub z c) eps) (k : Nat) :
    InInterval z.realPart (QInterval.expand (c.realPart.compute k) eps) ∧
    InInterval z.imagPart (QInterval.expand (c.imagPart.compute k) eps) := by
  constructor
  · apply inInterval_of_sub_bound (realPart_valid hz) (realPart_valid hc) eps
    · intro i j
      have b := h.1 i j
      change -eps ≤ (z.compute j).hi.re + -(c.compute j).lo.re at b
      change -eps ≤ (z.compute j).hi.re - (c.compute j).lo.re
      grind only [Rat.sub_eq_add_neg]
    · intro i j
      have b := h.2.1 i j
      change (z.compute i).lo.re + -(c.compute i).hi.re ≤ eps at b
      change (z.compute i).lo.re - (c.compute i).hi.re ≤ eps
      grind only [Rat.sub_eq_add_neg]
  · apply inInterval_of_sub_bound (imagPart_valid hz) (imagPart_valid hc) eps
    · intro i j
      have b := h.2.2.1 i j
      change -eps ≤ (z.compute j).hi.im + -(c.compute j).lo.im at b
      change -eps ≤ (z.compute j).hi.im - (c.compute j).lo.im
      grind only [Rat.sub_eq_add_neg]
    · intro i j
      have b := h.2.2.2 i j
      change (z.compute i).lo.im + -(c.compute i).hi.im ≤ eps at b
      change (z.compute i).lo.im - (c.compute i).hi.im ≤ eps
      grind only [Rat.sub_eq_add_neg]

/-- Coordinate observations include all valid complex neighbors in the
supplied domain. The real and imaginary output boxes share the identity
parametrization and are valid padded names of the existing value. -/
theorem ContinuousOn.hasEnclosureCoordinates {domain : ComplexRaw → Prop}
    {g : ComplexRaw → ComplexRaw} (h : ContinuousOn domain g)
    (valid : ∀ z, z.Valid → domain z → (g z).Valid)
    (a : ComplexRaw) (ha : a.Valid) (hda : domain a) :
    let delta := fun n => h.delta a ha hda ⟨allowance n,allowance_pos n⟩
    let tests := fun coordinate n y => ∃ z, z.Valid ∧ domain z ∧
      Small (sub z a) (runningRadius delta n).val ∧ y = coordinate (g z)
    HasEnclosureValue (tests ComplexRaw.realPart) (g a).realPart ∧
      HasEnclosureValue (tests ComplexRaw.imagPart) (g a).imagPart := by
  dsimp only
  let delta := fun n => h.delta a ha hda ⟨allowance n,allowance_pos n⟩
  have v := valid a ha hda
  constructor
  · refine ⟨realPart_valid v,(fun n m => QInterval.expand ((g a).realPart.compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,
      enlarged_valid (realPart_valid v),enlarged_equiv (realPart_valid v),?_⟩
    rintro k y ⟨z,hz,hdz,near,hy⟩
    rw [hy]
    exact (small_sub_coordinate_enclosures (valid z hz hdz) v
      (h.estimate a ha hda ⟨allowance k,allowance_pos k⟩ z hz hdz
        (near.mono (runningRadius_le delta k))) k).1
  · refine ⟨imagPart_valid v,(fun n m => QInterval.expand ((g a).imagPart.compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,
      enlarged_valid (imagPart_valid v),enlarged_equiv (imagPart_valid v),?_⟩
    rintro k y ⟨z,hz,hdz,near,hy⟩
    rw [hy]
    exact (small_sub_coordinate_enclosures (valid z hz hdz) v
      (h.estimate a ha hda ⟨allowance k,allowance_pos k⟩ z hz hdz
        (near.mono (runningRadius_le delta k))) k).2

theorem small_zero_enclosures {z : ComplexRaw} {eps : Rat} (h : Small z eps) (k : Nat) :
    InInterval z.realPart (QInterval.expand ((RealRaw.ofRat 0).compute k) eps) ∧
    InInterval z.imagPart (QInterval.expand ((RealRaw.ofRat 0).compute k) eps) := by
  constructor
  · constructor
    · intro i j
      have b := h.1 i j
      change (0:Rat)-eps ≤ (z.compute j).hi.re
      change -eps ≤ (z.compute j).hi.re at b
      grind only
    · intro i j
      have b := h.2.1 i j
      change (z.compute i).lo.re ≤ (0:Rat)+eps
      change (z.compute i).lo.re ≤ eps at b
      grind only
  · constructor
    · intro i j
      have b := h.2.2.1 i j
      change (0:Rat)-eps ≤ (z.compute j).hi.im
      change -eps ≤ (z.compute j).hi.im at b
      grind only
    · intro i j
      have b := h.2.2.2 i j
      change (z.compute i).lo.im ≤ (0:Rat)+eps
      change (z.compute i).lo.im ≤ eps at b
      grind only

theorem normalized_small {z : ComplexRaw} (H : QPos) (eps : Rat)
    (h : Small z (eps*H.val)) : Small (scaleRat (1/H.val) z) eps := by
  have hi : 0 ≤ 1/H.val := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr H.property))
  have eq : (1/H.val)*(eps*H.val)=eps := by
    have hn := Rat.ne_of_gt H.property
    rw [Rat.div_def,Rat.one_mul]
    calc
      H.val⁻¹*(eps*H.val) = eps*(H.val*H.val⁻¹) := by
        grind only [Rat.mul_assoc,Rat.mul_comm]
      _ = eps := by rw [Rat.mul_inv_cancel _ hn,Rat.mul_one]
  simpa only [eq] using RiemannHilbert.LocalODE.small_scale hi h

/-- First-order complex evidence supplies valid diagonals for normalized
remainders in every direction. The limit value is exact zero; no derivative
continuity, power series, or directional sampling is assumed. -/
theorem HasDerivativeAt.hasRemainderCoordinates {f : Map} {a d : ComplexRaw}
    (h : HasDerivativeAt f a d) :
    let delta := fun n => h.delta ⟨allowance n,allowance_pos n⟩
    let tests := fun coordinate n y => ∃ H : QPos, ∃ z, z.Valid ∧ f.domain z ∧
      H.val ≤ (runningRadius delta n).val ∧ Small (sub z a) H.val ∧
      y = coordinate (scaleRat (1/H.val) (remainder f a d z))
    HasEnclosureValue (tests ComplexRaw.realPart) (RealRaw.ofRat 0) ∧
      HasEnclosureValue (tests ComplexRaw.imagPart) (RealRaw.ofRat 0) := by
  dsimp only
  let delta := fun n => h.delta ⟨allowance n,allowance_pos n⟩
  have v := RealRaw.ofRat_valid 0
  constructor
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨H,z,hz,hdz,near,step,hy⟩
    rw [hy]
    have bound := normalized_small H (allowance k)
      (h.estimate ⟨allowance k,allowance_pos k⟩ H z hz hdz
        (Rat.le_trans near (runningRadius_le delta k)) step)
    exact (small_zero_enclosures bound k).1
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨H,z,hz,hdz,near,step,hy⟩
    rw [hy]
    have bound := normalized_small H (allowance k)
      (h.estimate ⟨allowance k,allowance_pos k⟩ H z hz hdz
        (Rat.le_trans near (runningRadius_le delta k)) step)
    exact (small_zero_enclosures bound k).2

end ComputableAnalysis.FunctionTheory

namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open RawLimit ComplexRaw FunctionTheory

/-- The domain-evidence interface used by modular and Riemann--Hilbert work
has the same coordinate enclosure bridge. Evaluation stays proof-dependent. -/
theorem ContinuousOn.hasEnclosureCoordinates {domain : Scalar → Prop}
    {g : ∀ z, domain z → Scalar} (h : ContinuousOn domain g)
    (a : Scalar) (ha : domain a) :
    let delta := fun n => h.delta a ha ⟨allowance n,allowance_pos n⟩
    let tests := fun coordinate n y => ∃ z hz,
      Small (sub z.val a.val) (runningRadius delta n).val ∧
      y = coordinate (g z hz).val
    HasEnclosureValue (tests ComplexRaw.realPart) (g a ha).val.realPart ∧
      HasEnclosureValue (tests ComplexRaw.imagPart) (g a ha).val.imagPart := by
  dsimp only
  let delta := fun n => h.delta a ha ⟨allowance n,allowance_pos n⟩
  have v := (g a ha).property
  constructor
  · refine ⟨realPart_valid v,(fun n m => QInterval.expand ((g a ha).val.realPart.compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,
      enlarged_valid (realPart_valid v),enlarged_equiv (realPart_valid v),?_⟩
    rintro k y ⟨z,hz,near,hy⟩
    rw [hy]
    exact (small_sub_coordinate_enclosures (g z hz).property v
      (h.estimate a ha ⟨allowance k,allowance_pos k⟩ z hz
        (near.mono (runningRadius_le delta k))) k).1
  · refine ⟨imagPart_valid v,(fun n m => QInterval.expand ((g a ha).val.imagPart.compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,
      enlarged_valid (imagPart_valid v),enlarged_equiv (imagPart_valid v),?_⟩
    rintro k y ⟨z,hz,near,hy⟩
    rw [hy]
    exact (small_sub_coordinate_enclosures (g z hz).property v
      (h.estimate a ha ⟨allowance k,allowance_pos k⟩ z hz
        (near.mono (runningRadius_le delta k))) k).2

theorem HasDerivativeAt.hasRemainderCoordinates {f : Map} {a d : Scalar}
    {ha : f.domain a} (h : HasDerivativeAt f a ha d) :
    let delta := fun n => h.delta ⟨allowance n,allowance_pos n⟩
    let tests := fun coordinate n y => ∃ H : QPos, ∃ z hz,
      H.val ≤ (runningRadius delta n).val ∧ Small (sub z.val a.val) H.val ∧
      y = coordinate (scaleRat (1/H.val) (remainder f a ha d z hz))
    HasEnclosureValue (tests ComplexRaw.realPart) (RealRaw.ofRat 0) ∧
      HasEnclosureValue (tests ComplexRaw.imagPart) (RealRaw.ofRat 0) := by
  dsimp only
  let delta := fun n => h.delta ⟨allowance n,allowance_pos n⟩
  have v := RealRaw.ofRat_valid 0
  constructor
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨H,z,hz,near,step,hy⟩
    rw [hy]
    have bound := normalized_small H (allowance k)
      (h.estimate ⟨allowance k,allowance_pos k⟩ H z hz
        (Rat.le_trans near (runningRadius_le delta k)) step)
    exact (small_zero_enclosures bound k).1
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨H,z,hz,near,step,hy⟩
    rw [hy]
    have bound := normalized_small H (allowance k)
      (h.estimate ⟨allowance k,allowance_pos k⟩ H z hz
        (Rat.le_trans near (runningRadius_le delta k)) step)
    exact (small_zero_enclosures bound k).2

end ComputableAnalysis.RiemannHilbert.DomainFunctions
