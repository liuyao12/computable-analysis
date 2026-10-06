import ComputableAnalysis.ModularForms.AllIdealsPrincipal163

/-! The only ambiguity of a nonzero principal ideal generator is its sign. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

theorem mul_neg_one (u : QuadraticOrder163) : mul u (neg one)=neg u := by
  apply ext <;> simp only [mul,neg,one] <;> grind

theorem principal_generators_eq_or_neg (u v : QuadraticOrder163) (hu : u≠zero)
    (hideal : ∀ z, InPrincipalIdeal u z ↔ InPrincipalIdeal v z) : u=v ∨ u=neg v := by
  have humem : InPrincipalIdeal u u := ⟨one,(mul_one u).symm⟩
  have hvmem : InPrincipalIdeal v v := ⟨one,(mul_one v).symm⟩
  obtain ⟨a,ha⟩ := (hideal u).mp humem
  obtain ⟨b,hb⟩ := (hideal v).mpr hvmem
  have he : mul u (mul b a)=mul u one := by
    rw [← mul_assoc,← hb,← ha,mul_one]
  have hunit : mul b a=one := mul_left_cancel u _ _ hu he
  have hba : IsUnit a := ⟨b,by rw [mul_comm]; exact hunit⟩
  have haunit := (isUnit_iff a).mp hba
  rcases haunit with hone | hneg
  · left
    rw [hone,mul_one] at ha
    exact ha
  · right
    rw [hneg,mul_neg_one] at ha
    exact ha

theorem principal_ideal_neg (u z : QuadraticOrder163) :
    InPrincipalIdeal (neg u) z ↔ InPrincipalIdeal u z := by
  have he (v : QuadraticOrder163) : mul (neg u) v=mul u (neg v) := by
    apply ext <;> simp only [mul,neg] <;> grind
  have hn (v : QuadraticOrder163) : neg (neg v)=v := by
    apply ext <;> simp only [neg] <;> omega
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨neg v,hv.trans (he v)⟩
  · rintro ⟨v,hv⟩
    refine ⟨neg v,?_⟩
    rw [he,hn]
    exact hv

theorem principal_ideals_eq_iff (u v : QuadraticOrder163) (hu : u≠zero) :
    (∀ z, InPrincipalIdeal u z ↔ InPrincipalIdeal v z) ↔ u=v ∨ u=neg v := by
  constructor
  · exact principal_generators_eq_or_neg u v hu
  · intro h z
    rcases h with h | h
    · rw [h]
    · rw [h]
      exact principal_ideal_neg v z

end ComputableAnalysis.ModularForms.QuadraticOrder163
