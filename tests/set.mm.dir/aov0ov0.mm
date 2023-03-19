include "cop.mm"
include "cafv.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "caov.mm"
include "co.mm"
include "afv0fv0.mm"
include "df-aov.mm"
include "eqeq1i.mm"
include "df-ov.mm"
include "3imtr4i.mm"

theorem aov0ov0
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (( A F B )) = (/) -> ( A F B ) = (/) )

  proof
    cA
    cB
    cop
    #
    cF
    cafv
    #
    c0
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
    c0
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
    afv0fv0
    @3
    @1
    c0
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
