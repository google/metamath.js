include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "uneq2.mm"
include "vex.mm"
include "unex.mm"
include "vtocl2g.mm"
include "wss.mm"
include "ssun1.mm"
include "ssexg.mm"
include "mpan.mm"
include "ssun2.mm"
include "jca.mm"
include "impbii.mm"

theorem unexb
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _V /\ B e. _V ) <-> ( A u. B ) e. _V )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cA
    cB
    cun
    #
    cvv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cvv
    wcel
    cA
    @5
    cun
    #
    cvv
    wcel
    @3
    vx
    vy
    cA
    cB
    cvv
    cvv
    @4
    cA
    wceq
    @6
    @7
    cvv
    @4
    cA
    @5
    uneq1
    eleq1d
    @5
    cB
    wceq
    @7
    @2
    cvv
    @5
    cB
    cA
    uneq2
    eleq1d
    @4
    @5
    vx
    vex
    vy
    vex
    unex
    vtocl2g
    @3
    @0
    @1
    cA
    @2
    wss
    @3
    @0
    cA
    cB
    ssun1
    cA
    @2
    cvv
    ssexg
    mpan
    cB
    @2
    wss
    @3
    @1
    cB
    cA
    ssun2
    cB
    @2
    cvv
    ssexg
    mpan
    jca
    impbii
end
