include "wcel.mm"
include "cfn.mm"
include "ccrd.mm"
include "cfv.mm"
include "com.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "isfi.mm"
include "wa.mm"
include "wceq.mm"
include "carden.mm"
include "wi.mm"
include "cardnn.mm"
include "eqtr.mm"
include "expcom.mm"
include "syl.mm"
include "eleq1a.mm"
include "syld.mm"
include "adantl.mm"
include "sylbird.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "eqcomd.mm"
include "mpbid.mm"
include "ex.mm"
include "ancld.mm"
include "breq2.mm"
include "rspcev.mm"
include "sylibr.mm"
include "syl6.mm"
include "impbid.mm"

theorem ficard
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. Fin <-> ( card ` A ) e. _om ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    ccrd
    cfv
    #
    com
    wcel
    #
    @1
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    #
    @0
    @3
    vx
    cA
    isfi
    #
    @0
    @5
    @3
    vx
    com
    @0
    @4
    com
    wcel
    #
    wa
    @5
    @2
    @4
    ccrd
    cfv
    #
    wceq
    #
    @3
    cA
    @4
    cV
    com
    carden
    @8
    @10
    @3
    wi
    @0
    @8
    @10
    @2
    @4
    wceq
    #
    @3
    @8
    @9
    @4
    wceq
    #
    @10
    @11
    wi
    @4
    cardnn
    @10
    @12
    @11
    @2
    @9
    @4
    eqtr
    expcom
    syl
    @4
    com
    @2
    eleq1a
    syld
    adantl
    sylbird
    rexlimdva
    syl5bi
    @0
    @3
    @3
    cA
    @2
    cen
    wbr
    #
    wa
    #
    @1
    @0
    @3
    @13
    @0
    @3
    @13
    @0
    @3
    wa
    @2
    @2
    ccrd
    cfv
    #
    wceq
    #
    @13
    @3
    @16
    @0
    @3
    @15
    @2
    @2
    cardnn
    eqcomd
    adantl
    cA
    @2
    cV
    com
    carden
    mpbid
    ex
    ancld
    @14
    @6
    @1
    @5
    @13
    vx
    @2
    com
    @4
    @2
    cA
    cen
    breq2
    rspcev
    @7
    sylibr
    syl6
    impbid
end
