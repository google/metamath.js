include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cwdom.mm"
include "wbr.mm"
include "cdom.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "brwdom.mm"
include "0domg.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "fodomnum.mm"
include "exlimdv.mm"
include "jaod.mm"
include "sylbid.mm"
include "domwdom.mm"
include "impbid1.mm"

theorem wdomnumr
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( B e. dom card -> ( A ~<_* B <-> A ~<_ B ) )

  proof
    cB
    ccrd
    cdm
    #
    wcel
    #
    cA
    cB
    cwdom
    wbr
    #
    cA
    cB
    cdom
    wbr
    #
    @1
    @2
    cA
    c0
    wceq
    #
    cB
    cA
    vx
    cv
    #
    wfo
    #
    vx
    wex
    #
    wo
    @3
    vx
    @0
    cA
    cB
    brwdom
    @1
    @4
    @3
    @7
    @1
    @3
    @4
    c0
    cB
    cdom
    wbr
    cB
    @0
    0domg
    cA
    c0
    cB
    cdom
    breq1
    syl5ibrcom
    @1
    @6
    @3
    vx
    cB
    cA
    @5
    fodomnum
    exlimdv
    jaod
    sylbid
    cA
    cB
    domwdom
    impbid1
end
