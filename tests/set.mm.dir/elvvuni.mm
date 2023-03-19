include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "cuni.mm"
include "elvv.mm"
include "cpr.mm"
include "vex.mm"
include "uniop.mm"
include "opi2.mm"
include "eqeltri.mm"
include "unieq.mm"
include "id.mm"
include "eleq12d.mm"
include "mpbiri.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem elvvuni
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. ( _V X. _V ) -> U. A e. A )

  proof
    cA
    cvv
    cvv
    cxp
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    cA
    cuni
    #
    cA
    wcel
    #
    vx
    vy
    cA
    elvv
    @3
    @5
    vx
    vy
    @3
    @5
    @2
    cuni
    #
    @2
    wcel
    @6
    @0
    @1
    cpr
    @2
    @0
    @1
    vx
    vex
    #
    vy
    vex
    #
    uniop
    @0
    @1
    @7
    @8
    opi2
    eqeltri
    @3
    @4
    @6
    cA
    @2
    cA
    @2
    unieq
    @3
    id
    eleq12d
    mpbiri
    exlimivv
    sylbi
end
