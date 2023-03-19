include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "con0.mm"
include "wrex.mm"
include "wral.mm"
include "cvv.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "eqid.mm"
include "tz9.12lem2.mm"
include "onsuci.mm"
include "tz9.12lem3.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "sylancr.mm"

theorem tz9.12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vv: setvar v
  assume tz9.12.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint v x
  disjoint y z
  disjoint v y
  disjoint v z
  disjoint A z
  disjoint A v
  assert |- ( A. x e. A E. y e. On x e. ( R1 ` y ) -> E. y e. On A e. ( R1 ` y ) )

  proof
    vx
    cv
    vy
    cv
    #
    cr1
    cfv
    #
    wcel
    vy
    con0
    wrex
    vx
    cA
    wral
    vz
    cvv
    vz
    cv
    vv
    cv
    cr1
    cfv
    wcel
    vv
    con0
    crab
    cint
    cmpt
    #
    cA
    cima
    cuni
    csuc
    #
    csuc
    #
    con0
    wcel
    cA
    @4
    cr1
    cfv
    #
    wcel
    #
    cA
    @1
    wcel
    #
    vy
    con0
    wrex
    @3
    vz
    vv
    cA
    @2
    tz9.12.1
    @2
    eqid
    #
    tz9.12lem2
    onsuci
    vx
    vy
    vz
    vv
    cA
    @2
    tz9.12.1
    @8
    tz9.12lem3
    @7
    @6
    vy
    @4
    con0
    @0
    @4
    wceq
    @1
    @5
    cA
    @0
    @4
    cr1
    fveq2
    eleq2d
    rspcev
    sylancr
end
