include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "weu.mm"
include "cfv.mm"
include "wceq.mm"
include "df-br.mm"
include "eubii.mm"
include "tz6.12-1.mm"
include "syl2anbr.mm"

theorem tz6.12
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint F y
  disjoint A y
  assert |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F ) -> ( F ` A ) = y )

  proof
    cA
    vy
    cv
    #
    cop
    cF
    wcel
    #
    cA
    @0
    cF
    wbr
    #
    @2
    vy
    weu
    cA
    cF
    cfv
    @0
    wceq
    @1
    vy
    weu
    cA
    @0
    cF
    df-br
    #
    @2
    @1
    vy
    @3
    eubii
    vy
    cA
    cF
    tz6.12-1
    syl2anbr
end
