include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cfv.mm"
include "wceq.mm"
include "wex.mm"
include "euex.mm"
include "wi.mm"
include "nfeu1.mm"
include "nfv.mm"
include "nfim.mm"
include "tz6.12-1.mm"
include "expcom.mm"
include "breq2.mm"
include "biimprd.mm"
include "syli.mm"
include "com12.mm"
include "exlimi.mm"
include "mpcom.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem tz6.12c
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint F y
  disjoint A y
  assert |- ( E! y A F y -> ( ( F ` A ) = y <-> A F y ) )

  proof
    cA
    vy
    cv
    #
    cF
    wbr
    #
    vy
    weu
    #
    cA
    cF
    cfv
    #
    @0
    wceq
    #
    @1
    @2
    cA
    @3
    cF
    wbr
    #
    @4
    @1
    @1
    vy
    wex
    @2
    @5
    @1
    vy
    euex
    @1
    @2
    @5
    wi
    vy
    @2
    @5
    vy
    @1
    vy
    nfeu1
    @5
    vy
    nfv
    nfim
    @2
    @1
    @5
    @1
    @2
    @4
    @5
    @1
    @2
    @4
    vy
    cA
    cF
    tz6.12-1
    expcom
    #
    @4
    @5
    @1
    @3
    @0
    cA
    cF
    breq2
    #
    biimprd
    syli
    com12
    exlimi
    mpcom
    @7
    syl5ibcom
    @6
    impbid
end
