include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "isfi.mm"
include "biimpi.mm"
include "wi.mm"
include "wa.mm"
include "wceq.mm"
include "cdm.mm"
include "finnum.mm"
include "cardid2.mm"
include "syl.mm"
include "entr.mm"
include "sylan.mm"
include "con0.mm"
include "wb.mm"
include "cardon.mm"
include "onomeneq.mm"
include "mpan.mm"
include "syl5ib.mm"
include "eleq1a.mm"
include "syld.mm"
include "expcomd.mm"
include "rexlimiv.mm"
include "mpcom.mm"

theorem ficardom
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Fin -> ( card ` A ) e. _om )

  proof
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
    @3
    @2
    vx
    cA
    isfi
    biimpi
    @1
    @3
    @5
    wi
    vx
    com
    @0
    com
    wcel
    #
    @3
    @1
    @5
    @6
    @3
    @1
    wa
    #
    @4
    @0
    wceq
    #
    @5
    @7
    @4
    @0
    cen
    wbr
    #
    @6
    @8
    @3
    @4
    cA
    cen
    wbr
    #
    @1
    @9
    @3
    cA
    ccrd
    cdm
    wcel
    @10
    cA
    finnum
    cA
    cardid2
    syl
    @4
    cA
    @0
    entr
    sylan
    @4
    con0
    wcel
    @6
    @9
    @8
    wb
    cA
    cardon
    @4
    @0
    onomeneq
    mpan
    syl5ib
    @0
    com
    @4
    eleq1a
    syld
    expcomd
    rexlimiv
    mpcom
end
