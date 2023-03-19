include "cv.mm"
include "cop.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "opeq1.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "opeq2.mm"
include "eqeq1d.mm"
include "vex.mm"
include "op1st.mm"
include "vtocl2g.mm"

theorem op1stg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( 1st ` <. A , B >. ) = A )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    c1st
    cfv
    #
    @0
    wceq
    cA
    @1
    cop
    #
    c1st
    cfv
    #
    cA
    wceq
    cA
    cB
    cop
    #
    c1st
    cfv
    #
    cA
    wceq
    vx
    vy
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    #
    @3
    @5
    @0
    cA
    @8
    @2
    @4
    c1st
    @0
    cA
    @1
    opeq1
    fveq2d
    @8
    id
    eqeq12d
    @1
    cB
    wceq
    #
    @5
    @7
    cA
    @9
    @4
    @6
    c1st
    @1
    cB
    cA
    opeq2
    fveq2d
    eqeq1d
    @0
    @1
    vx
    vex
    vy
    vex
    op1st
    vtocl2g
end
