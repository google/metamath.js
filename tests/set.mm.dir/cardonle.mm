include "con0.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "crab.mm"
include "cint.mm"
include "oncardval.mm"
include "wss.mm"
include "enrefg.mm"
include "breq1.mm"
include "intminss.mm"
include "mpdan.mm"
include "eqsstrd.mm"

theorem cardonle
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( card ` A ) C_ A )

  proof
    cA
    con0
    wcel
    #
    cA
    ccrd
    cfv
    vx
    cv
    #
    cA
    cen
    wbr
    #
    vx
    con0
    crab
    cint
    #
    cA
    vx
    cA
    oncardval
    @0
    cA
    cA
    cen
    wbr
    #
    @3
    cA
    wss
    cA
    con0
    enrefg
    @2
    @4
    vx
    cA
    con0
    @1
    cA
    cA
    cen
    breq1
    intminss
    mpdan
    eqsstrd
end
