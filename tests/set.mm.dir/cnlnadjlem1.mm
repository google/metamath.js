include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "chil.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem cnlnadjlem1
  let vy: setvar y
  let cA: class A
  let cT: class T
  let vg: setvar g
  let cG: class G
  let vf: setvar f
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vt: setvar t
  let vx: setvar x
  let cF: class F
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )

  disjoint g y
  disjoint A g
  disjoint A y
  disjoint T g
  disjoint T y
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g v
  disjoint g w
  disjoint g z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w y
  disjoint w z
  disjoint A w
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
  disjoint F w
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
  disjoint T v
  disjoint T w
  disjoint x y
  disjoint T x
  disjoint T z
  disjoint C f
  disjoint G f
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G z
  assert |- ( A e. ~H -> ( G ` A ) = ( ( T ` A ) .ih y ) )

  proof
    vg
    cA
    vg
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    csp
    co
    cA
    cT
    cfv
    #
    @2
    csp
    co
    chil
    cG
    @0
    cA
    wceq
    @1
    @3
    @2
    csp
    @0
    cA
    cT
    fveq2
    oveq1d
    cnlnadjlem.3
    @3
    @2
    csp
    ovex
    fvmpt
end
