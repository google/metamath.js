include "cima.mm"
include "crn.mm"
include "con0.mm"
include "imassrn.mm"
include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "cvv.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "id.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "eqvisset.mm"
include "intex.mm"
include "sylibr.mm"
include "oninton.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "rexlimivw.mm"
include "abssi.mm"
include "eqsstri.mm"
include "sstri.mm"

theorem tz9.12lem1
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume tz9.12lem.1: |- A e. _V
  assume tz9.12lem.2: |- F = ( z e. _V |-> |^| { v e. On | z e. ( R1 ` v ) } )

  disjoint v z
  disjoint A z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint v y
  disjoint A y
  disjoint F x
  disjoint F y
  assert |- ( F " A ) C_ On

  proof
    cF
    cA
    cima
    cF
    crn
    #
    con0
    cF
    cA
    imassrn
    @0
    vx
    cv
    #
    vz
    cv
    vv
    cv
    cr1
    cfv
    wcel
    #
    vv
    con0
    crab
    #
    cint
    #
    wceq
    #
    vz
    cvv
    wrex
    #
    vx
    cab
    con0
    vz
    vx
    cvv
    @4
    cF
    tz9.12lem.2
    rnmpt
    @6
    vx
    con0
    @5
    @1
    con0
    wcel
    vz
    cvv
    @5
    @1
    @4
    con0
    @5
    id
    @5
    @3
    con0
    wss
    @3
    c0
    wne
    #
    @4
    con0
    wcel
    @2
    vv
    con0
    ssrab2
    @5
    @4
    cvv
    wcel
    @7
    vx
    @4
    eqvisset
    @3
    intex
    sylibr
    @3
    oninton
    sylancr
    eqeltrd
    rexlimivw
    abssi
    eqsstri
    sstri
end
