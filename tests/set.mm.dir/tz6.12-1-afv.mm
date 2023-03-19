include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "weu.mm"
include "cafv.mm"
include "wceq.mm"
include "df-br.mm"
include "eubii.mm"
include "tz6.12-afv.mm"
include "syl2anb.mm"

theorem tz6.12-1-afv
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vk: setvar k

  disjoint A y
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint F x
  disjoint k x
  assert |- ( ( A F y /\ E! y A F y ) -> ( F ''' A ) = y )

  proof
    cA
    vy
    cv
    #
    cF
    wbr
    #
    cA
    @0
    cop
    cF
    wcel
    #
    @2
    vy
    weu
    cA
    cF
    cafv
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
    @1
    @2
    vy
    @3
    eubii
    vy
    cA
    cF
    tz6.12-afv
    syl2anb
end
