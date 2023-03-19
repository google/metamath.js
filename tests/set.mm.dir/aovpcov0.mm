include "cop.mm"
include "cafv.mm"
include "cvv.mm"
include "wceq.mm"
include "cfv.mm"
include "c0.mm"
include "caov.mm"
include "co.mm"
include "afvpcfv0.mm"
include "df-aov.mm"
include "eqeq1i.mm"
include "df-ov.mm"
include "3imtr4i.mm"

theorem aovpcov0
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (( A F B )) = _V -> ( A F B ) = (/) )

  proof
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cvv
    wceq
    @0
    cF
    cfv
    #
    c0
    wceq
    cA
    cB
    cF
    caov
    #
    cvv
    wceq
    cA
    cB
    cF
    co
    #
    c0
    wceq
    @0
    cF
    afvpcfv0
    @3
    @1
    cvv
    cA
    cB
    cF
    df-aov
    eqeq1i
    @4
    @2
    c0
    cA
    cB
    cF
    df-ov
    eqeq1i
    3imtr4i
end
