include "cv.mm"
include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "uneq1d.mm"
include "eqeq12d.mm"
include "uneq2.mm"
include "uneq2d.mm"
include "vex.mm"
include "rankun.mm"
include "vtocl2g.mm"

theorem rankung
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( rank ` ( A u. B ) ) = ( ( rank ` A ) u. ( rank ` B ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    crnk
    cfv
    #
    @0
    crnk
    cfv
    #
    @1
    crnk
    cfv
    #
    cun
    #
    wceq
    cA
    @1
    cun
    #
    crnk
    cfv
    #
    cA
    crnk
    cfv
    #
    @5
    cun
    #
    wceq
    cA
    cB
    cun
    #
    crnk
    cfv
    #
    @9
    cB
    crnk
    cfv
    #
    cun
    #
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
    @8
    @6
    @10
    @15
    @2
    @7
    crnk
    @0
    cA
    @1
    uneq1
    fveq2d
    @15
    @4
    @9
    @5
    @0
    cA
    crnk
    fveq2
    uneq1d
    eqeq12d
    @1
    cB
    wceq
    #
    @8
    @12
    @10
    @14
    @16
    @7
    @11
    crnk
    @1
    cB
    cA
    uneq2
    fveq2d
    @16
    @5
    @13
    @9
    @1
    cB
    crnk
    fveq2
    uneq2d
    eqeq12d
    @0
    @1
    vx
    vex
    vy
    vex
    rankun
    vtocl2g
end
