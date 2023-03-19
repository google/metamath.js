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
include "com.mm"
include "wss.mm"
include "elwina.mm"
include "con0.mm"
include "cfon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "winainflem.mm"
include "syl3an2.mm"
include "sylbi.mm"

theorem winainf
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. InaccW -> _om C_ A )

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
    com
    cA
    wss
    #
    vx
    vy
    cA
    elwina
    @2
    @0
    cA
    con0
    wcel
    #
    @3
    @4
    @2
    @1
    con0
    wcel
    @5
    cA
    cfon
    @1
    cA
    con0
    eleq1
    mpbii
    vx
    vy
    cA
    winainflem
    syl3an2
    sylbi
end
