include "cv.mm"
include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "wceq.mm"
include "preq1.mm"
include "unieqd.mm"
include "uneq1.mm"
include "eqeq12d.mm"
include "preq2.mm"
include "uneq2.mm"
include "vex.mm"
include "unipr.mm"
include "vtocl2g.mm"

theorem uniprg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> U. { A , B } = ( A u. B ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cuni
    #
    @0
    @1
    cun
    #
    wceq
    cA
    @1
    cpr
    #
    cuni
    #
    cA
    @1
    cun
    #
    wceq
    cA
    cB
    cpr
    #
    cuni
    #
    cA
    cB
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
    @6
    @4
    @7
    @11
    @2
    @5
    @0
    cA
    @1
    preq1
    unieqd
    @0
    cA
    @1
    uneq1
    eqeq12d
    @1
    cB
    wceq
    #
    @6
    @9
    @7
    @10
    @12
    @5
    @8
    @1
    cB
    cA
    preq2
    unieqd
    @1
    cB
    cA
    uneq2
    eqeq12d
    @0
    @1
    vx
    vex
    vy
    vex
    unipr
    vtocl2g
end
