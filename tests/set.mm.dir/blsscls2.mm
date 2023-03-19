include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cle.mm"
include "crab.mm"
include "cbl.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "simplr3.mm"
include "xmetcl.mm"
include "3expa.mm"
include "adantlr.mm"
include "simplr1.mm"
include "simplr2.mm"
include "xrlelttr.mm"
include "expcomd.mm"
include "syl3anc.mm"
include "mpd.mm"
include "wb.mm"
include "simp2.mm"
include "elbl2.mm"
include "an4s.mm"
include "sylanr1.mm"
include "anassrs.mm"
include "sylibrd.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "syl5eqss.mm"

theorem blsscls2
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vr: setvar r
  let vw: setvar w
  let cN: class N
  assume mopni.1: |- J = ( MetOpen ` D )
  assume blcld.3: |- S = { z e. X | ( P D z ) <_ R }

  disjoint D z
  disjoint R z
  disjoint P z
  disjoint T z
  disjoint X z
  disjoint x y
  disjoint A x
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
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint N r
  disjoint N y
  disjoint P r
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint X r
  disjoint X w
  disjoint X x
  disjoint X y
  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X ) /\ ( R e. RR* /\ T e. RR* /\ R < T ) ) -> S C_ ( P ( ball ` D ) T ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cR
    cxr
    wcel
    #
    cT
    cxr
    wcel
    #
    cR
    cT
    clt
    wbr
    #
    w3a
    #
    wa
    #
    cS
    cP
    vz
    cv
    #
    cD
    co
    #
    cR
    cle
    wbr
    #
    vz
    cX
    crab
    #
    cP
    cT
    cD
    cbl
    cfv
    co
    #
    blcld.3
    @7
    @10
    @8
    @12
    wcel
    #
    wi
    #
    vz
    cX
    wral
    @11
    @12
    wss
    @7
    @14
    vz
    cX
    @7
    @8
    cX
    wcel
    #
    wa
    #
    @10
    @9
    cT
    clt
    wbr
    #
    @13
    @16
    @5
    @10
    @17
    wi
    #
    @3
    @4
    @5
    @2
    @15
    simplr3
    @16
    @9
    cxr
    wcel
    #
    @3
    @4
    @5
    @18
    wi
    @2
    @15
    @19
    @6
    @0
    @1
    @15
    @19
    cP
    @8
    cD
    cX
    xmetcl
    3expa
    adantlr
    @3
    @4
    @5
    @2
    @15
    simplr1
    @3
    @4
    @5
    @2
    @15
    simplr2
    @19
    @3
    @4
    w3a
    @10
    @5
    @17
    @9
    cR
    cT
    xrlelttr
    expcomd
    syl3anc
    mpd
    @2
    @6
    @15
    @13
    @17
    wb
    #
    @6
    @2
    @4
    @15
    @20
    @3
    @4
    @5
    simp2
    @0
    @4
    @1
    @15
    @20
    @8
    cD
    cP
    cT
    cX
    elbl2
    an4s
    sylanr1
    anassrs
    sylibrd
    ralrimiva
    @10
    vz
    cX
    @12
    rabss
    sylibr
    syl5eqss
end
