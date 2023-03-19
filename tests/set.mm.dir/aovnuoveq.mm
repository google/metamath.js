include "caov.mm"
include "cvv.mm"
include "wne.mm"
include "cop.mm"
include "cafv.mm"
include "co.mm"
include "wceq.mm"
include "df-aov.mm"
include "neeq1i.mm"
include "cfv.mm"
include "afvnufveq.mm"
include "df-ov.mm"
include "3eqtr4g.mm"
include "sylbi.mm"

theorem aovnuoveq
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (( A F B )) =/= _V -> (( A F B )) = ( A F B ) )

  proof
    cA
    cB
    cF
    caov
    #
    cvv
    wne
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cvv
    wne
    #
    @0
    cA
    cB
    cF
    co
    #
    wceq
    @0
    @2
    cvv
    cA
    cB
    cF
    df-aov
    #
    neeq1i
    @3
    @2
    @1
    cF
    cfv
    @0
    @4
    @1
    cF
    afvnufveq
    @5
    cA
    cB
    cF
    df-ov
    3eqtr4g
    sylbi
end
