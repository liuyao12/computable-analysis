import ComputableAnalysis.ModularForms.NormalizedIdeal163

/-! Integer scaling of concrete principal and normalized ideal lattices. -/
namespace ComputableAnalysis.ModularForms
open QuadraticOrder163

theorem order163_scale_mul (d : Int) (u v : QuadraticOrder163) :
    scale d (mul u v)=mul (scale d u) v := by
  apply QuadraticOrder163.ext <;> simp only [scale,mul] <;> grind

theorem order163_scale_norm (d : Int) (u : QuadraticOrder163) :
    norm (scale d u)=d*d*norm u := by
  unfold norm scale
  grind

def InScaledNormalizedIdeal163 (d a t : Int) (z : QuadraticOrder163) : Prop :=
  ∃ m n : Int, z=scale d (normalizedIdealLattice163 a t m n)

theorem scaledNormalizedIdeal163_principal (d a t c : Int) (ha : 0<a)
    (hc : t*t+t+41=a*c) (z : QuadraticOrder163) :
    InScaledNormalizedIdeal163 d a t z ↔
      InPrincipalIdeal (scale d (normalizedIdealForm163 a t c ha hc).idealGenerator) z := by
  let f := normalizedIdealForm163 a t c ha hc
  constructor
  · rintro ⟨m,n,h⟩
    have hi : InNormalizedIdeal163 a t (normalizedIdealLattice163 a t m n) := ⟨m,n,rfl⟩
    have hp := (normalizedIdeal163_principal a t c ha hc _).mp hi
    obtain ⟨v,hv⟩ := hp
    refine ⟨v,?_⟩
    rw [h,hv,order163_scale_mul]
  · rintro ⟨v,hv⟩
    have hp : InPrincipalIdeal f.idealGenerator (mul f.idealGenerator v) := ⟨v,rfl⟩
    have hi := (normalizedIdeal163_principal a t c ha hc _).mpr hp
    obtain ⟨m,n,hi⟩ := hi
    refine ⟨m,n,?_⟩
    rw [hv,← order163_scale_mul,hi]

theorem scaledNormalizedIdeal163_exists_generator (d a t : Int) (ha : 0<a)
    (hdiv : a ∣ t*t+t+41) :
    ∃ u : QuadraticOrder163, norm u=d*d*a ∧
      ∀ z, InScaledNormalizedIdeal163 d a t z ↔ InPrincipalIdeal u z := by
  obtain ⟨c,hc⟩ := hdiv
  let f := normalizedIdealForm163 a t c ha hc
  refine ⟨scale d f.idealGenerator,?_,?_⟩
  · rw [order163_scale_norm,f.idealGenerator_norm]
    rfl
  · intro z
    exact scaledNormalizedIdeal163_principal d a t c ha hc z

end ComputableAnalysis.ModularForms
