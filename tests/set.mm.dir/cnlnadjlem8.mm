include "ccop.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cnop.mm"
include "nmcopexi.mm"
include "cnlnadjlem7.mm"
include "rgen.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "cnlnadjlem6.mm"
include "lnopconi.mm"
include "mpbir.mm"

theorem cnlnadjlem8
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vz: setvar z
  let cA: class A
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
  disjoint v w
  disjoint v y
  disjoint w y
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
  disjoint A g
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
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
  assert |- F e. ContOp

  proof
    cF
    ccop
    wcel
    vz
    cv
    #
    cF
    cfv
    cno
    cfv
    #
    vx
    cv
    #
    @0
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vz
    chil
    wral
    #
    vx
    cr
    wrex
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    @1
    @8
    @3
    cmul
    co
    #
    cle
    wbr
    #
    vz
    chil
    wral
    #
    @7
    cT
    cnlnadjlem.1
    cnlnadjlem.2
    nmcopexi
    @10
    vz
    chil
    vy
    vw
    vv
    @0
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
    cnlnadjlem7
    rgen
    @6
    @11
    vx
    @8
    cr
    @2
    @8
    wceq
    #
    @5
    @10
    vz
    chil
    @12
    @4
    @9
    @1
    cle
    @2
    @8
    @3
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    mp2an
    vx
    vz
    cF
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
    lnopconi
    mpbir
end
