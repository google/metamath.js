include "chil.mm"
include "cnlnadjlem3.mm"
include "fmpti.mm"
include "ffvelrni.mm"

theorem cnlnadjlem4
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vz: setvar z
  let vt: setvar t
  let vx: setvar x
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )
  assume cnlnadjlem.4: |- B = ( iota_ w e. ~H A. v e. ~H ( ( T ` v ) .ih y ) = ( v .ih w ) )
  assume cnlnadjlem.5: |- F = ( y e. ~H |-> B )

  disjoint g v
  disjoint g w
  disjoint g y
  disjoint A g
  disjoint v w
  disjoint v y
  disjoint A v
  disjoint w y
  disjoint A w
  disjoint A y
  disjoint F w
  disjoint T g
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint G v
  disjoint G w
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g z
  disjoint v z
  disjoint w z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint T f
  disjoint g t
  disjoint g x
  disjoint t v
  disjoint t y
  disjoint T t
  disjoint v x
  disjoint x y
  disjoint T x
  disjoint T z
  disjoint C f
  disjoint G f
  disjoint G x
  disjoint G z
  assert |- ( A e. ~H -> ( F ` A ) e. ~H )

  proof
    chil
    chil
    cA
    cF
    vy
    chil
    chil
    cB
    cF
    cnlnadjlem.5
    vy
    vw
    vv
    cB
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem3
    fmpti
    ffvelrni
end
