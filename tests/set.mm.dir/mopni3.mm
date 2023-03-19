include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "crp.mm"
include "wa.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "mopni2.mm"
include "adantr.mm"
include "simp1.mm"
include "mopnss.mm"
include "sselda.mm"
include "3impa.mm"
include "jca.mm"
include "ssblex.mm"
include "sylan.mm"
include "anassrs.mm"
include "sstr.mm"
include "expcom.mm"
include "anim2d.mm"
include "reximdv.mm"
include "syl5com.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem mopni3
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  let cN: class N
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )

  disjoint A x
  disjoint D x
  disjoint J x
  disjoint R x
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
  assert |- ( ( ( D e. ( *Met ` X ) /\ A e. J /\ P e. A ) /\ R e. RR+ ) -> E. x e. RR+ ( x < R /\ ( P ( ball ` D ) x ) C_ A ) )

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
    #
    cR
    crp
    wcel
    #
    wa
    #
    cP
    vy
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    cA
    wss
    #
    vy
    crp
    wrex
    #
    vx
    cv
    #
    cR
    clt
    wbr
    #
    cP
    @11
    @7
    co
    #
    cA
    wss
    #
    wa
    #
    vx
    crp
    wrex
    #
    @3
    @10
    @4
    vy
    cA
    cD
    cP
    cJ
    cX
    mopni.1
    mopni2
    adantr
    @5
    @9
    @16
    vy
    crp
    @5
    @6
    crp
    wcel
    #
    wa
    @12
    @13
    @8
    wss
    #
    wa
    #
    vx
    crp
    wrex
    #
    @9
    @16
    @3
    @4
    @17
    @20
    @3
    @0
    cP
    cX
    wcel
    #
    wa
    @4
    @17
    wa
    @20
    @3
    @0
    @21
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    @21
    @0
    @1
    wa
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
    3impa
    jca
    vx
    cD
    cP
    cR
    @6
    cX
    ssblex
    sylan
    anassrs
    @9
    @19
    @15
    vx
    crp
    @9
    @18
    @14
    @12
    @18
    @9
    @14
    @13
    @8
    cA
    sstr
    expcom
    anim2d
    reximdv
    syl5com
    rexlimdva
    mpd
end
