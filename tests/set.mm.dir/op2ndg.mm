include "cv.mm"
include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "opeq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "opeq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "vex.mm"
include "op2nd.mm"
include "vtocl2g.mm"

theorem op2ndg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( 2nd ` <. A , B >. ) = B )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    c2nd
    cfv
    #
    @1
    wceq
    cA
    @1
    cop
    #
    c2nd
    cfv
    #
    @1
    wceq
    cA
    cB
    cop
    #
    c2nd
    cfv
    #
    cB
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
    @1
    @8
    @2
    @4
    c2nd
    @0
    cA
    @1
    opeq1
    fveq2d
    eqeq1d
    @1
    cB
    wceq
    #
    @5
    @7
    @1
    cB
    @9
    @4
    @6
    c2nd
    @1
    cB
    cA
    opeq2
    fveq2d
    @9
    id
    eqeq12d
    @0
    @1
    vx
    vex
    vy
    vex
    op2nd
    vtocl2g
end
