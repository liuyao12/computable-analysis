import ComputableAnalysis.ModularForms.CMFiniteAnnuli163

/-! Integral changes of basis on the explicit CM lattice indices. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def basisIndex (g : SL2Z) (u : QuadraticOrder163) : QuadraticOrder163 :=
  ⟨g.a*u.x+g.b*u.y,g.c*u.x+g.d*u.y⟩

theorem basisIndex_identity (u : QuadraticOrder163) : basisIndex SL2Z.identity u=u := by
  apply ext <;> simp [basisIndex,SL2Z.identity]

theorem basisIndex_compose (g h : SL2Z) (u : QuadraticOrder163) :
    basisIndex g (basisIndex h u)=basisIndex (SL2Z.multiply g h) u := by
  apply ext <;> simp only [basisIndex,SL2Z.multiply] <;> grind

theorem basisIndex_inverse (g : SL2Z) (u : QuadraticOrder163) :
    basisIndex (SL2Z.inverse g) (basisIndex g u)=u := by
  rw [basisIndex_compose,SL2Z.inverse_multiply,basisIndex_identity]

theorem basisIndex_injective (g : SL2Z) (u v : QuadraticOrder163)
    (h : basisIndex g u=basisIndex g v) : u=v := by
  have he := congrArg (basisIndex (SL2Z.inverse g)) h
  simpa only [basisIndex_inverse] using he

theorem basisIndex_nonzero (g : SL2Z) (u : QuadraticOrder163) (hu : u≠zero) :
    basisIndex g u≠zero := by
  intro h
  have hz : basisIndex g zero=zero := by apply ext <;> simp [basisIndex,zero]
  exact hu (basisIndex_injective g u zero (h.trans hz.symm))

/-- An executable bound on the coordinate enlargement of a basis change. -/
def basisRadiusFactor (g : SL2Z) : Nat := g.a.natAbs+g.b.natAbs+g.c.natAbs+g.d.natAbs

private theorem product_bounds (a x r : Int) (hr : 0≤r) (hx : -r≤x ∧ x≤r) :
    -(a.natAbs:Int)*r≤a*x ∧ a*x≤(a.natAbs:Int)*r := by
  have ha : a≤(a.natAbs:Int) := Int.le_natAbs
  have han : -(a.natAbs:Int)≤a := by
    have h : -a≤((-a).natAbs:Int) := Int.le_natAbs
    rw [Int.natAbs_neg] at h
    omega
  by_cases hp : 0≤a
  · have h1 := Int.mul_le_mul_of_nonneg_left hx.1 hp
    have h2 := Int.mul_le_mul_of_nonneg_left hx.2 hp
    have h3 := Int.mul_le_mul_of_nonneg_right ha hr
    grind
  · have hp' : 0≤ -a := by omega
    have h1 := Int.mul_le_mul_of_nonneg_left hx.1 hp'
    have h2 := Int.mul_le_mul_of_nonneg_left hx.2 hp'
    have h3 := Int.mul_le_mul_of_nonneg_right (show -a≤(a.natAbs:Int) by omega) hr
    grind

theorem basisIndex_radius_le (g : SL2Z) (u : QuadraticOrder163) :
    shellRadius (basisIndex g u)≤basisRadiusFactor g*shellRadius u := by
  have h := shellRadius_bounds u
  have hr : 0≤(shellRadius u:Int) := by omega
  have ha := product_bounds g.a u.x _ hr ⟨h.1,h.2.1⟩
  have hb := product_bounds g.b u.y _ hr ⟨h.2.2.1,h.2.2.2.1⟩
  have hc := product_bounds g.c u.x _ hr ⟨h.1,h.2.1⟩
  have hd := product_bounds g.d u.y _ hr ⟨h.2.2.1,h.2.2.2.1⟩
  have hmissing1 : 0≤((g.c.natAbs+g.d.natAbs:Nat):Int)*(shellRadius u:Int) :=
    Int.mul_nonneg (by omega) hr
  have hmissing2 : 0≤((g.a.natAbs+g.b.natAbs:Nat):Int)*(shellRadius u:Int) :=
    Int.mul_nonneg (by omega) hr
  apply (shellRadius_le_iff _ _).mpr
  simp only [basisIndex,basisRadiusFactor,Int.natCast_add,Int.natCast_mul] at *
  grind

theorem basisIndex_square_nodup (g : SL2Z) (N : Nat) :
    ((squarePoints N).map (basisIndex g)).Nodup := by
  apply List.Pairwise.map (basisIndex g) _ (squarePoints_nodup N)
  intro u v huv he
  exact huv (basisIndex_injective g u v he)

theorem basisIndex_square_enclosure (g : SL2Z) (N : Nat) (u : QuadraticOrder163)
    (hu : u ∈ squarePoints N) : basisIndex g u ∈ squarePoints (basisRadiusFactor g*N) := by
  have h := (mem_squarePoints u N).mp hu
  apply (mem_squarePoints _ _).mpr
  have hb := basisIndex_radius_le g u
  have hm := Nat.mul_le_mul_left (basisRadiusFactor g) h.2
  exact ⟨basisIndex_nonzero g u h.1,by omega⟩

end ComputableAnalysis.ModularForms.QuadraticOrder163
