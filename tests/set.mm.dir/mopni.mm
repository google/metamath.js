include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "elmopn.mm"
include "simplbda.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "syl.mm"
include "3impia.mm"

theorem mopni
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cP: class P
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cN: class N
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )

  disjoint A x
  disjoint D x
  disjoint J x
  disjoint P x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J r
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint N r
  disjoint N y
  disjoint P r
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint T z
  disjoint X r
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( *Met ` X ) /\ A e. J /\ P e. A ) -> E. x e. ran ( ball ` D ) ( P e. x /\ x C_ A ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cJ
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    @3
    cA
    wss
    #
    wa
    #
    vx
    cD
    cbl
    cfv
    crn
    #
    wrex
    #
    @0
    @1
    wa
    vy
    cv
    #
    @3
    wcel
    #
    @5
    wa
    #
    vx
    @7
    wrex
    #
    vy
    cA
    wral
    #
    @2
    @8
    wi
    @0
    @1
    cA
    cX
    wss
    @13
    vy
    vx
    cA
    cD
    cJ
    cX
    mopni.1
    elmopn
    simplbda
    @12
    @8
    vy
    cP
    cA
    @9
    cP
    wceq
    #
    @11
    @6
    vx
    @7
    @14
    @10
    @4
    @5
    @9
    cP
    @3
    eleq1
    anbi1d
    rexbidv
    rspccv
    syl
    3impia
end
