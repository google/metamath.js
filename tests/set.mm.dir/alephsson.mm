include "cale.mm"
include "crn.mm"
include "con0.mm"
include "cv.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "isinfcard.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "adantl.mm"
include "sylbir.mm"
include "ssriv.mm"

theorem alephsson
  let vx: setvar x


  assert |- ran aleph C_ On

  proof
    vx
    cale
    crn
    #
    con0
    vx
    cv
    #
    @0
    wcel
    com
    @1
    wss
    #
    @1
    ccrd
    cfv
    #
    @1
    wceq
    #
    wa
    @1
    con0
    wcel
    #
    @1
    isinfcard
    @4
    @5
    @2
    @4
    @3
    con0
    wcel
    @5
    @1
    cardon
    @3
    @1
    con0
    eleq1
    mpbii
    adantl
    sylbir
    ssriv
end
