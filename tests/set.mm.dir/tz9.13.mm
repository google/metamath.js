include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "wss.mm"
include "wi.mm"
include "wceq.mm"
include "setind.mm"
include "wral.mm"
include "ssel.mm"
include "vex.mm"
include "eleq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "syl6ib.mm"
include "ralrimiv.mm"
include "tz9.12.mm"
include "syl.mm"
include "sylibr.mm"
include "mpg.mm"
include "eleqtrri.mm"
include "mpbi.mm"

theorem tz9.13
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume tz9.13.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- E. x e. On A e. ( R1 ` x )

  proof
    cA
    vy
    cv
    #
    vx
    cv
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    wrex
    #
    vy
    cab
    #
    wcel
    cA
    @1
    wcel
    #
    vx
    con0
    wrex
    #
    cA
    cvv
    @4
    tz9.13.1
    vz
    cv
    #
    @4
    wss
    #
    @7
    @4
    wcel
    #
    wi
    @4
    cvv
    wceq
    vz
    vz
    @4
    setind
    @8
    @7
    @1
    wcel
    #
    vx
    con0
    wrex
    #
    @9
    @8
    vw
    cv
    #
    @1
    wcel
    #
    vx
    con0
    wrex
    #
    vw
    @7
    wral
    @11
    @8
    @14
    vw
    @7
    @8
    @12
    @7
    wcel
    @12
    @4
    wcel
    @14
    @7
    @4
    @12
    ssel
    @3
    @14
    vy
    @12
    vw
    vex
    @0
    @12
    wceq
    @2
    @13
    vx
    con0
    @0
    @12
    @1
    eleq1
    rexbidv
    elab
    syl6ib
    ralrimiv
    vw
    vx
    @7
    vz
    vex
    #
    tz9.12
    syl
    @3
    @11
    vy
    @7
    @15
    @0
    @7
    wceq
    @2
    @10
    vx
    con0
    @0
    @7
    @1
    eleq1
    rexbidv
    elab
    sylibr
    mpg
    eleqtrri
    @3
    @6
    vy
    cA
    tz9.13.1
    @0
    cA
    wceq
    @2
    @5
    vx
    con0
    @0
    cA
    @1
    eleq1
    rexbidv
    elab
    mpbi
end
