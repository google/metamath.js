include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wss.mm"
include "r1elssi.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "tz9.12.mm"
include "dfss3.mm"
include "ciun.mm"
include "wfn.mm"
include "wfun.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "funiunfv.mm"
include "mp2b.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "bitri.mm"
include "3imtr4i.mm"
include "impbii.mm"

theorem r1elss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume r1elss.1: |- A e. _V


  assert |- ( A e. U. ( R1 " On ) <-> A C_ U. ( R1 " On ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    @0
    wss
    #
    cA
    r1elssi
    vy
    cv
    #
    vx
    cv
    cr1
    cfv
    #
    wcel
    vx
    con0
    wrex
    #
    vy
    cA
    wral
    #
    cA
    @4
    wcel
    vx
    con0
    wrex
    #
    @2
    @1
    vy
    vx
    cA
    r1elss.1
    tz9.12
    @2
    @3
    @0
    wcel
    #
    vy
    cA
    wral
    @6
    vy
    cA
    @0
    dfss3
    @8
    @5
    vy
    cA
    @8
    @3
    vx
    con0
    @4
    ciun
    #
    wcel
    @5
    @9
    @0
    @3
    cr1
    con0
    wfn
    cr1
    wfun
    @9
    @0
    wceq
    r1fnon
    con0
    cr1
    fnfun
    vx
    con0
    cr1
    funiunfv
    mp2b
    #
    eleq2i
    vx
    @3
    con0
    @4
    eliun
    bitr3i
    ralbii
    bitri
    @1
    cA
    @9
    wcel
    @7
    @9
    @0
    cA
    @10
    eleq2i
    vx
    cA
    con0
    @4
    eliun
    bitr3i
    3imtr4i
    impbii
end
