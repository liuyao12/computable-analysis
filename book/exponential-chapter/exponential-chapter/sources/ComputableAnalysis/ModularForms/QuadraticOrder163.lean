import ComputableAnalysis.ModularForms.Form163Primitive

/-! Concrete integral arithmetic with omega squared equal to omega minus 41. -/
namespace ComputableAnalysis.ModularForms

structure QuadraticOrder163 where
  x : Int
  y : Int
  deriving DecidableEq

namespace QuadraticOrder163

@[ext] theorem ext {u v : QuadraticOrder163} (hx : u.x=v.x) (hy : u.y=v.y) :
    u=v := by cases u; cases v; simp_all

def zero : QuadraticOrder163 := ⟨0,0⟩
def one : QuadraticOrder163 := ⟨1,0⟩
def omega : QuadraticOrder163 := ⟨0,1⟩
def add (u v : QuadraticOrder163) : QuadraticOrder163 := ⟨u.x+v.x,u.y+v.y⟩
def neg (u : QuadraticOrder163) : QuadraticOrder163 := ⟨-u.x,-u.y⟩
def mul (u v : QuadraticOrder163) : QuadraticOrder163 :=
  ⟨u.x*v.x-41*u.y*v.y,u.x*v.y+u.y*v.x+u.y*v.y⟩
def conjugate (u : QuadraticOrder163) : QuadraticOrder163 := ⟨u.x+u.y,-u.y⟩
def norm (u : QuadraticOrder163) : Int := u.x*u.x+u.x*u.y+41*u.y*u.y

theorem omega_square : mul omega omega=add omega ⟨-41,0⟩ := by decide

theorem mul_assoc (u v w : QuadraticOrder163) : mul (mul u v) w=mul u (mul v w) := by
  apply ext <;> simp only [mul] <;> grind

theorem mul_comm (u v : QuadraticOrder163) : mul u v=mul v u := by
  apply ext <;> simp only [mul] <;> grind

theorem mul_one (u : QuadraticOrder163) : mul u one=u := by
  apply ext <;> simp [mul,one]

theorem mul_add (u v w : QuadraticOrder163) : mul u (add v w)=add (mul u v) (mul u w) := by
  apply ext <;> simp only [mul,add] <;> grind

theorem conjugate_involution (u : QuadraticOrder163) : conjugate (conjugate u)=u := by
  apply ext <;> simp only [conjugate] <;> omega

theorem conjugate_mul (u v : QuadraticOrder163) :
    conjugate (mul u v)=mul (conjugate u) (conjugate v) := by
  apply ext <;> simp only [conjugate,mul] <;> grind

theorem mul_conjugate (u : QuadraticOrder163) : mul u (conjugate u)=⟨norm u,0⟩ := by
  apply ext <;> simp only [mul,conjugate,norm] <;> grind

theorem norm_mul (u v : QuadraticOrder163) : norm (mul u v)=norm u*norm v := by
  unfold norm mul
  grind

theorem norm_eq_principal (u : QuadraticOrder163) :
    norm u=principalIntegralForm163.eval u.x u.y := by
  simp [norm,principalIntegralForm163,IntegralForm163.eval]

theorem norm_positive (u : QuadraticOrder163) (hu : u≠zero) : 0<norm u := by
  rw [norm_eq_principal]
  apply principalIntegralForm163.eval_positive
  by_cases hx : u.x=0
  · right
    intro hy
    apply hu
    exact ext hx hy
  · exact Or.inl hx

theorem norm_eq_zero_iff (u : QuadraticOrder163) : norm u=0 ↔ u=zero := by
  constructor
  · intro hn
    by_cases hu : u=zero
    · exact hu
    · have hp := norm_positive u hu
      omega
  · intro hu
    rw [hu]
    decide

end QuadraticOrder163
end ComputableAnalysis.ModularForms
