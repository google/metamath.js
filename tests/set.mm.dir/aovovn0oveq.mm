include "co.mm"
include "c0.mm"
include "wne.mm"
include "cop.mm"
include "cfv.mm"
include "caov.mm"
include "wceq.mm"
include "df-ov.mm"
include "neeq1i.mm"
include "cafv.mm"
include "afvfvn0fveq.mm"
include "df-aov.mm"
include "3eqtr4g.mm"
include "sylbi.mm"

theorem aovovn0oveq
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A F B ) =/= (/) -> (( A F B )) = ( A F B ) )

  proof
    cA
    cB
    cF
    co
    #
    c0
    wne
    cA
    cB
    cop
    #
    cF
    cfv
    #
    c0
    wne
    #
    cA
    cB
    cF
    caov
    #
    @0
    wceq
    @0
    @2
    c0
    cA
    cB
    cF
    df-ov
    #
    neeq1i
    @3
    @1
    cF
    cafv
    @2
    @4
    @0
    @1
    cF
    afvfvn0fveq
    cA
    cB
    cF
    df-aov
    @5
    3eqtr4g
    sylbi
end
