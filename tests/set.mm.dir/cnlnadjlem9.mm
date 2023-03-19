include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wrex.mm"
include "cnlnadjlem6.mm"
include "cnlnadjlem8.mm"
include "elin.mm"
include "mpbir2an.mm"
include "cnlnadjlem5.mm"
include "ancoms.mm"
include "rgen2a.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"

theorem cnlnadjlem9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cB: class B
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vf: setvar f
  let cA: class A
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )
  assume cnlnadjlem.4: |- B = ( iota_ w e. ~H A. v e. ~H ( ( T ` v ) .ih y ) = ( v .ih w ) )
  assume cnlnadjlem.5: |- F = ( y e. ~H |-> B )

  disjoint g v
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint B z
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint g t
  disjoint g x
  disjoint T g
  disjoint t v
  disjoint t y
  disjoint T t
  disjoint v x
  disjoint T v
  disjoint T w
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G z
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint A g
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint T f
  disjoint C f
  disjoint G f
  assert |- E. t e. ( LinOp i^i ContOp ) A. x e. ~H A. z e. ~H ( ( T ` x ) .ih z ) = ( x .ih ( t ` z ) )

  proof
    cF
    clo
    ccop
    cin
    #
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    vz
    cv
    #
    csp
    co
    #
    @2
    @3
    cF
    cfv
    #
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    @4
    @2
    @3
    vt
    cv
    #
    cfv
    #
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    vt
    @0
    wrex
    @1
    cF
    clo
    wcel
    cF
    ccop
    wcel
    vy
    vw
    vv
    cB
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem6
    vy
    vw
    vv
    cB
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem8
    cF
    clo
    ccop
    elin
    mpbir2an
    @7
    vx
    vz
    chil
    @3
    chil
    wcel
    @2
    chil
    wcel
    @7
    vy
    vw
    vv
    @3
    cB
    @2
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem5
    ancoms
    rgen2a
    @13
    @8
    vt
    cF
    @0
    @9
    cF
    wceq
    #
    @12
    @7
    vx
    vz
    chil
    chil
    @14
    @11
    @6
    @4
    @14
    @10
    @5
    @2
    csp
    @3
    @9
    cF
    fveq1
    oveq2d
    eqeq2d
    2ralbidv
    rspcev
    mp2an
end
