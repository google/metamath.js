include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "co.mm"
include "crp.mm"
include "mopni.mm"
include "wb.mm"
include "mopnss.mm"
include "sselda.mm"
include "blssex.mm"
include "adantlr.mm"
include "syldan.mm"
include "3impa.mm"
include "mpbid.mm"

theorem mopni2
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
  assert |- ( ( D e. ( *Met ` X ) /\ A e. J /\ P e. A ) -> E. x e. RR+ ( P ( ball ` D ) x ) C_ A )

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
    w3a
    cP
    vy
    cv
    #
    wcel
    @3
    cA
    wss
    wa
    vy
    cD
    cbl
    cfv
    #
    crn
    wrex
    #
    cP
    vx
    cv
    @4
    co
    cA
    wss
    vx
    crp
    wrex
    #
    vy
    cA
    cD
    cP
    cJ
    cX
    mopni.1
    mopni
    @0
    @1
    @2
    @5
    @6
    wb
    #
    @0
    @1
    wa
    #
    @2
    cP
    cX
    wcel
    #
    @7
    @8
    cA
    cX
    cP
    cA
    cD
    cJ
    cX
    mopni.1
    mopnss
    sselda
    @0
    @9
    @7
    @1
    vy
    cA
    cD
    cP
    cX
    vx
    blssex
    adantlr
    syldan
    3impa
    mpbid
end
