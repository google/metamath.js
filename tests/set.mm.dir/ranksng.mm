include "cv.mm"
include "csn.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "wceq.mm"
include "sneq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "suceq.mm"
include "syl.mm"
include "eqeq12d.mm"
include "vex.mm"
include "ranksn.mm"
include "vtoclg.mm"

theorem ranksng
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. V -> ( rank ` { A } ) = suc ( rank ` A ) )

  proof
    vx
    cv
    #
    csn
    #
    crnk
    cfv
    #
    @0
    crnk
    cfv
    #
    csuc
    #
    wceq
    cA
    csn
    #
    crnk
    cfv
    #
    cA
    crnk
    cfv
    #
    csuc
    #
    wceq
    vx
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @6
    @4
    @8
    @9
    @1
    @5
    crnk
    @0
    cA
    sneq
    fveq2d
    @9
    @3
    @7
    wceq
    @4
    @8
    wceq
    @0
    cA
    crnk
    fveq2
    @3
    @7
    suceq
    syl
    eqeq12d
    @0
    vx
    vex
    ranksn
    vtoclg
end
