include "wpo.mm"
include "wcel.mm"
include "wa.mm"
include "cpred.mm"
include "wss.mm"
include "predel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wb.mm"
include "elpredg.mm"
include "adantll.mm"
include "potr.mm"
include "3exp2.mm"
include "com24.mm"
include "imp31.mm"
include "com13.mm"
include "ex.mm"
include "com14.mm"
include "sylbid.mm"
include "com23.mm"
include "3imp.mm"
include "imdistand.mm"
include "vex.mm"
include "elpred.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "3exp.mm"
include "mpdi.mm"

theorem predpo
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vz: setvar z


  assert |- ( ( R Po A /\ X e. A ) -> ( Y e. Pred ( R , A , X ) -> Pred ( R , A , Y ) C_ Pred ( R , A , X ) ) )

  proof
    cA
    cR
    wpo
    #
    cX
    cA
    wcel
    #
    wa
    #
    cY
    cA
    cR
    cX
    cpred
    #
    wcel
    #
    cY
    cA
    wcel
    #
    cA
    cR
    cY
    cpred
    #
    @3
    wss
    #
    cA
    cR
    cX
    cY
    predel
    @2
    @4
    @5
    @7
    @2
    @4
    @5
    w3a
    #
    vz
    @6
    @3
    @8
    vz
    cv
    #
    cA
    wcel
    #
    @9
    cY
    cR
    wbr
    #
    wa
    #
    @10
    @9
    cX
    cR
    wbr
    #
    wa
    #
    @9
    @6
    wcel
    #
    @9
    @3
    wcel
    #
    @8
    @10
    @11
    @13
    @2
    @4
    @5
    @10
    @11
    @13
    wi
    wi
    #
    @2
    @5
    @4
    @17
    @2
    @5
    @4
    @17
    wi
    @2
    @5
    wa
    #
    @4
    cY
    cX
    cR
    wbr
    #
    @17
    @1
    @5
    @4
    @19
    wb
    @0
    cA
    cA
    cR
    cX
    cY
    elpredg
    adantll
    @11
    @19
    @10
    @18
    @13
    @11
    @19
    @10
    @18
    @13
    wi
    wi
    @18
    @10
    @11
    @19
    wa
    #
    @13
    @0
    @1
    @5
    @10
    @20
    @13
    wi
    #
    wi
    @0
    @10
    @5
    @1
    @21
    @0
    @10
    @5
    @1
    @21
    cA
    @9
    cY
    cX
    cR
    potr
    3exp2
    com24
    imp31
    com13
    ex
    com14
    sylbid
    ex
    com23
    3imp
    imdistand
    @5
    @2
    @15
    @12
    wb
    @4
    cA
    cA
    cR
    cY
    @9
    vz
    vex
    #
    elpred
    3ad2ant3
    @2
    @4
    @16
    @14
    wb
    #
    @5
    @1
    @23
    @0
    cA
    cA
    cR
    cX
    @9
    @22
    elpred
    adantl
    3ad2ant1
    3imtr4d
    ssrdv
    3exp
    mpdi
end
