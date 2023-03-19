include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cardval3.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "onint.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"

theorem cardid2
  let cA: class A
  let vy: setvar y


  assert |- ( A e. dom card -> ( card ` A ) ~~ A )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    ccrd
    cfv
    #
    vy
    cv
    #
    cA
    cen
    wbr
    #
    vy
    con0
    crab
    #
    wcel
    #
    @1
    cA
    cen
    wbr
    #
    @0
    @1
    @4
    cint
    #
    @4
    vy
    cA
    cardval3
    #
    @0
    @4
    con0
    wss
    @4
    c0
    wne
    #
    @7
    @4
    wcel
    @3
    vy
    con0
    ssrab2
    @0
    @7
    cvv
    wcel
    @9
    @0
    @7
    @1
    cvv
    @8
    cA
    ccrd
    fvex
    syl6eqelr
    @4
    intex
    sylibr
    @4
    onint
    sylancr
    eqeltrd
    @5
    @1
    con0
    wcel
    @6
    @3
    @6
    vy
    @1
    con0
    @2
    @1
    cA
    cen
    breq1
    elrab
    simprbi
    syl
end
