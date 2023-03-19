include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wa.mm"
include "cfv.mm"
include "cio.mm"
include "df-fv.mm"
include "wceq.mm"
include "iota1.mm"
include "biimpac.mm"
include "syl5eq.mm"

theorem tz6.12-1
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint F y
  disjoint A y
  assert |- ( ( A F y /\ E! y A F y ) -> ( F ` A ) = y )

  proof
    cA
    vy
    cv
    #
    cF
    wbr
    #
    @1
    vy
    weu
    #
    wa
    cA
    cF
    cfv
    @1
    vy
    cio
    #
    @0
    vy
    cA
    cF
    df-fv
    @2
    @1
    @3
    @0
    wceq
    @1
    vy
    iota1
    biimpac
    syl5eq
end
