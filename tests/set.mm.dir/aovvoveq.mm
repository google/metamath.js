include "caov.mm"
include "wcel.mm"
include "cop.mm"
include "cafv.mm"
include "co.mm"
include "wceq.mm"
include "df-aov.mm"
include "eleq1i.mm"
include "cfv.mm"
include "afvvfveq.mm"
include "df-ov.mm"
include "3eqtr4g.mm"
include "sylbi.mm"

theorem aovvoveq
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (( A F B )) e. C -> (( A F B )) = ( A F B ) )

  proof
    cA
    cB
    cF
    caov
    #
    cC
    wcel
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cC
    wcel
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
    cC
    cA
    cB
    cF
    df-aov
    #
    eleq1i
    @3
    @2
    @1
    cF
    cfv
    @0
    @4
    @1
    cC
    cF
    afvvfveq
    @5
    cA
    cB
    cF
    df-ov
    3eqtr4g
    sylbi
end
