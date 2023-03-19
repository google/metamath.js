include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "cafv.mm"
include "cvv.mm"
include "wo.mm"
include "caov.mm"
include "df-ov.mm"
include "eqeq1i.mm"
include "afvfv0bi.mm"
include "df-aov.mm"
include "bicomi.mm"
include "orbi12i.mm"
include "3bitri.mm"

theorem aovov0bi
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A F B ) = (/) <-> ( (( A F B )) = (/) \/ (( A F B )) = _V ) )

  proof
    cA
    cB
    cF
    co
    #
    c0
    wceq
    cA
    cB
    cop
    #
    cF
    cfv
    #
    c0
    wceq
    @1
    cF
    cafv
    #
    c0
    wceq
    #
    @3
    cvv
    wceq
    #
    wo
    cA
    cB
    cF
    caov
    #
    c0
    wceq
    #
    @6
    cvv
    wceq
    #
    wo
    @0
    @2
    c0
    cA
    cB
    cF
    df-ov
    eqeq1i
    @1
    cF
    afvfv0bi
    @4
    @7
    @5
    @8
    @7
    @4
    @6
    @3
    c0
    cA
    cB
    cF
    df-aov
    #
    eqeq1i
    bicomi
    @8
    @5
    @6
    @3
    cvv
    @9
    eqeq1i
    bicomi
    orbi12i
    3bitri
end
