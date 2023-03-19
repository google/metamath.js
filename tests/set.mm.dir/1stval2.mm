include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "c1st.mm"
include "cfv.mm"
include "cint.mm"
include "elvv.mm"
include "vex.mm"
include "op1st.mm"
include "op1stb.mm"
include "eqtr4i.mm"
include "fveq2.mm"
include "inteq.mm"
include "inteqd.mm"
include "3eqtr4a.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem 1stval2
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. ( _V X. _V ) -> ( 1st ` A ) = |^| |^| A )

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
    c1st
    cfv
    #
    cA
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
    @7
    vx
    vy
    @3
    @2
    c1st
    cfv
    #
    @2
    cint
    #
    cint
    #
    @4
    @6
    @8
    @0
    @10
    @0
    @1
    vx
    vex
    #
    vy
    vex
    #
    op1st
    @0
    @1
    @11
    @12
    op1stb
    eqtr4i
    cA
    @2
    c1st
    fveq2
    @3
    @5
    @9
    cA
    @2
    inteq
    inteqd
    3eqtr4a
    exlimivv
    sylbi
end
