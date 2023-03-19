include "wfun.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "funrel.mm"
include "brrelex2.mm"
include "sylan.mm"
include "cv.mm"
include "wi.mm"
include "breq2.mm"
include "anbi2d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "weu.mm"
include "funeu.mm"
include "tz6.12-1.mm"
include "sylan2.mm"
include "anabss7.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "ex.mm"

theorem funbrfv
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y


  assert |- ( Fun F -> ( A F B -> ( F ` A ) = B ) )

  proof
    cF
    wfun
    #
    cA
    cB
    cF
    wbr
    #
    cA
    cF
    cfv
    #
    cB
    wceq
    #
    cB
    cvv
    wcel
    #
    @0
    @1
    wa
    #
    @3
    @0
    cF
    wrel
    @1
    @4
    cF
    funrel
    cA
    cB
    cF
    brrelex2
    sylan
    @0
    cA
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    @2
    @6
    wceq
    #
    wi
    @5
    @3
    wi
    vy
    cB
    cvv
    @6
    cB
    wceq
    #
    @8
    @5
    @9
    @3
    @10
    @7
    @1
    @0
    @6
    cB
    cA
    cF
    breq2
    anbi2d
    @6
    cB
    @2
    eqeq2
    imbi12d
    @0
    @7
    @9
    @8
    @7
    @7
    vy
    weu
    @9
    vy
    cA
    @6
    cF
    funeu
    vy
    cA
    cF
    tz6.12-1
    sylan2
    anabss7
    vtoclg
    mpcom
    ex
end
