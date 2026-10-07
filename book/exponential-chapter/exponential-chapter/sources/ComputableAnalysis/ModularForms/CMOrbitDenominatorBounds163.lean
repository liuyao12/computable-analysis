import ComputableAnalysis.ModularForms.CMOrbitSquarePrefixes163
import ComputableAnalysis.ModularForms.CMLatticeBounds163

/-! Executable denominator-power bounds for CM-orbit lattice constructions. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def cmOrbitDenominatorBound163 (g : SL2Z) : Rat := 82*(shellRadius ⟨g.d,g.c⟩:Rat)

theorem cmOrbitDenominatorBound163_nonnegative (g : SL2Z) : 0≤cmOrbitDenominatorBound163 g := by
  apply Rat.mul_nonneg (by decide +kernel)
  exact_mod_cast Nat.zero_le (shellRadius ⟨g.d,g.c⟩)

theorem cmOrbitDenominator163_small (g : SL2Z) :
    Small (cmOrbitDenominator163 g).val (cmOrbitDenominatorBound163 g) := by
  have h := shellRadius_bounds (⟨g.d,g.c⟩ : QuadraticOrder163)
  apply complexRaw_small (⟨g.d,g.c⟩ : QuadraticOrder163)
    (shellRadius ⟨g.d,g.c⟩:Rat) (by exact_mod_cast Nat.zero_le (shellRadius ⟨g.d,g.c⟩))
  · exact ⟨by simpa only [Rat.intCast_neg,Rat.intCast_natCast] using Rat.intCast_le_intCast.mpr h.1,by exact_mod_cast h.2.1⟩
  · exact ⟨by simpa only [Rat.intCast_neg,Rat.intCast_natCast] using Rat.intCast_le_intCast.mpr h.2.2.1,by exact_mod_cast h.2.2.2.1⟩

def cmOrbitPowerBound163 (g : SL2Z) (k : Nat) : Rat := (2*cmOrbitDenominatorBound163 g)^k

theorem cmOrbitPowerBound163_nonnegative (g : SL2Z) (k : Nat) : 0≤cmOrbitPowerBound163 g k :=
  Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (cmOrbitDenominatorBound163_nonnegative g))

theorem cmOrbitDenominatorPower163_small (g : SL2Z) (k : Nat) :
    Small (LocalODE.power (cmOrbitDenominator163 g).val k) (cmOrbitPowerBound163 g k) :=
  LocalODE.power_small _ (cmOrbitDenominator163 g).property _
    (cmOrbitDenominatorBound163_nonnegative g) (cmOrbitDenominator163_small g) k

/-- Fixed-factor multiplication transports a quantitative difference bound. -/
theorem representedFactor_difference_small (c F p : ComplexRaw)
    (hc : c.Valid) (hF : F.Valid) (hp : p.Valid) (M E : Rat)
    (hM : 0≤M) (hE : 0≤E) (hcM : Small c M) (hclose : Small (ComplexRaw.sub F p) E) :
    Small (ComplexRaw.sub (ComplexRaw.mul c F) (ComplexRaw.mul c p)) (2*M*E) := by
  have he : (ComplexRaw.mul c (ComplexRaw.sub F p)).Equiv
      (ComplexRaw.sub (ComplexRaw.mul c F) (ComplexRaw.mul c p)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.mul_valid hc (ComplexRaw.sub_valid hF hp))
      (hright := ComplexRaw.sub_valid (ComplexRaw.mul_valid hc hF) (ComplexRaw.mul_valid hc hp))
    change ComplexRawQuotient.ofRaw c hc*(ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)=
      ComplexRawQuotient.ofRaw c hc*ComplexRawQuotient.ofRaw F hF-
        ComplexRawQuotient.ofRaw c hc*ComplexRawQuotient.ofRaw p hp
    grind
  have hb := Small.mul hc (ComplexRaw.sub_valid hF hp) hM hE hcM hclose
  exact Small.congr (ComplexRaw.mul_valid hc (ComplexRaw.sub_valid hF hp))
    (ComplexRaw.sub_valid (ComplexRaw.mul_valid hc hF) (ComplexRaw.mul_valid hc hp)) he hb

end ComputableAnalysis.ModularForms
