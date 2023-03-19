include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "c2nd.mm"
include "cfv.mm"
include "csn.mm"
include "ccnv.mm"
include "cint.mm"
include "elvv.mm"
include "vex.mm"
include "op2nd.mm"
include "op2ndb.mm"
include "eqtr4i.mm"
include "fveq2.mm"
include "sneq.mm"
include "cnveqd.mm"
include "inteqd.mm"
include "3eqtr4a.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem 2ndval2
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. ( _V X. _V ) -> ( 2nd ` A ) = |^| |^| |^| `' { A } )

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
    c2nd
    cfv
    #
    cA
    csn
    #
    ccnv
    #
    cint
    #
    cint
    #
    cint
    #
    wceq
    #
    vx
    vy
    cA
    elvv
    @3
    @10
    vx
    vy
    @3
    @2
    c2nd
    cfv
    #
    @2
    csn
    #
    ccnv
    #
    cint
    #
    cint
    #
    cint
    #
    @4
    @9
    @11
    @1
    @16
    @0
    @1
    vx
    vex
    #
    vy
    vex
    #
    op2nd
    @0
    @1
    @17
    @18
    op2ndb
    eqtr4i
    cA
    @2
    c2nd
    fveq2
    @3
    @8
    @15
    @3
    @7
    @14
    @3
    @6
    @13
    @3
    @5
    @12
    cA
    @2
    sneq
    cnveqd
    inteqd
    inteqd
    inteqd
    3eqtr4a
    exlimivv
    sylbi
end
