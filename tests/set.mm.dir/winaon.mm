include "cwina.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "con0.mm"
include "elwina.mm"
include "cfon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "3ad2ant2.mm"
include "sylbi.mm"

theorem winaon
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. InaccW -> A e. On )

  proof
    cA
    cwina
    wcel
    cA
    c0
    wne
    #
    cA
    ccf
    cfv
    #
    cA
    wceq
    #
    vx
    cv
    vy
    cv
    csdm
    wbr
    vy
    cA
    wrex
    vx
    cA
    wral
    #
    w3a
    cA
    con0
    wcel
    #
    vx
    vy
    cA
    elwina
    @2
    @0
    @4
    @3
    @2
    @1
    con0
    wcel
    @4
    cA
    cfon
    @1
    cA
    con0
    eleq1
    mpbii
    3ad2ant2
    sylbi
end
