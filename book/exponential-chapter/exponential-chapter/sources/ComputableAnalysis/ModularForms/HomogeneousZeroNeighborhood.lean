import ComputableAnalysis.ModularForms.HomogeneousLocalUniqueness

/-! Constructed zero neighborhoods for actual holomorphic homogeneous solutions. -/
namespace ComputableAnalysis.ModularForms.HomogeneousZeroNeighborhood
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000
noncomputable section

variable (f g : DomainFunctions.Map) (hf : Holomorphic f) (hg : Holomorphic g)
  (hfg : ∀ z, f.domain z → g.domain z) (a : Scalar) (ha : f.domain a)

def coefficientBound : QPos :=
  ⟨1+scalarBound (g.eval a (hfg a ha)),by have h := scalarBound_pos (g.eval a (hfg a ha)); grind only⟩

def valueContinuous : ContinuousAt f a ha := (hf.atPoint a ha).continuousAt

def coefficientContinuous : ContinuousAt g a (hfg a ha) := (hg.atPoint a (hfg a ha)).continuousAt

def radius : QPos :=
  minRadius (hf.openDomain.radius a ha)
    (minRadius ((coefficientContinuous f g hg hfg a ha).delta unitError)
      (minRadius ((valueContinuous f hf a ha).delta unitError)
        (divideRadius ⟨1/16,by decide +kernel⟩ (coefficientBound f g hfg a ha))))

theorem mem (z : Scalar) (hz : HomogeneousLocalUniqueness.Neighborhood a (radius f g hf hg hfg a ha) z) :
    f.domain z := hf.openDomain.inside a ha z (hz.mono (minRadius_left _ _))

theorem short : 8*(coefficientBound f g hfg a ha).val*(radius f g hf hg hfg a ha).val≤(1:Rat)/2 := by
  have hr : (radius f g hf hg hfg a ha).val≤
      (divideRadius ⟨1/16,by decide +kernel⟩ (coefficientBound f g hfg a ha)).val := Rat.le_trans (minRadius_right _ _)
    (Rat.le_trans (minRadius_right _ _) (minRadius_right _ _))
  have hm := Rat.mul_le_mul_of_nonneg_left hr (Rat.le_of_lt (coefficientBound f g hfg a ha).property)
  rw [divideRadius_identity] at hm
  grind only

theorem coefficient_bound (z : Scalar)
    (hz : HomogeneousLocalUniqueness.Neighborhood a (radius f g hf hg hfg a ha) z) :
    Small (g.eval z (hfg z (mem f g hf hg hfg a ha z hz))).val (coefficientBound f g hfg a ha).val := by
  let hm := mem f g hf hg hfg a ha z hz
  let v := g.eval z (hfg z hm)
  let c := g.eval a (hfg a ha)
  have hc := scalar_small c
  have hd := (coefficientContinuous f g hg hfg a ha).estimate unitError z (hfg z hm)
    (hz.mono (Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)))
  have hs := LocalODE.small_add hd hc
  have he : (add (sub v.val c.val) c.val).Equiv v.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid v.property c.property) c.property) (hright := v.property)
    let V := gridScalarValue v
    let C := gridScalarValue c
    change (V-C)+C=V
    grind only
  exact Small.congr (add_valid (sub_valid v.property c.property) c.property) v.property he hs

include hg hfg in
theorem value_bound (hzero : (f.eval a ha).val.Equiv zero) (z : Scalar)
    (hz : HomogeneousLocalUniqueness.Neighborhood a (radius f g hf hg hfg a ha) z) :
    Small (f.eval z (mem f g hf hg hfg a ha z hz)).val 1 := by
  let hm := mem f g hf hg hfg a ha z hz
  let v := f.eval z hm
  let c := f.eval a ha
  have hd := (valueContinuous f hf a ha).estimate unitError z hm
    (hz.mono (Rat.le_trans (minRadius_right _ _)
      (Rat.le_trans (minRadius_right _ _) (minRadius_left _ _))))
  have he : (sub v.val c.val).Equiv v.val := by
    have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := c.property) (hright := ofQComplex_valid _) hzero
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid v.property c.property) (hright := v.property)
    let V := gridScalarValue v
    let C := gridScalarValue c
    change C=0 at h0
    change V-C=V
    rw [h0]
    grind only
  exact Small.congr (sub_valid v.property c.property) v.property he hd

theorem zero_neighborhood
    (heq : ∀ z hz, (hf.derivative z hz).val.Equiv
      (mul (g.eval z (hfg z hz)).val (f.eval z hz).val))
    (hzero : (f.eval a ha).val.Equiv zero) (z : Scalar)
    (hz : HomogeneousLocalUniqueness.Neighborhood a (radius f g hf hg hfg a ha) z) :
    (f.eval z (mem f g hf hg hfg a ha z hz)).val.Equiv zero :=
  HomogeneousLocalUniqueness.zero_on f hf a ha (radius f g hf hg hfg a ha)
    (mem f g hf hg hfg a ha) (fun z hz => g.eval z (hfg z hz))
    (coefficientBound f g hfg a ha).val (coefficientBound f g hfg a ha).property
    (short f g hf hg hfg a ha) (coefficient_bound f g hf hg hfg a ha) heq hzero
    unitError (value_bound f g hf hg hfg a ha hzero) z hz

end
end ComputableAnalysis.ModularForms.HomogeneousZeroNeighborhood
