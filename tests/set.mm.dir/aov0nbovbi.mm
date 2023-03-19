include "c0.mm"
include "wnel.mm"
include "cop.mm"
include "cafv.mm"
include "wcel.mm"
include "cfv.mm"
include "caov.mm"
include "co.mm"
include "afv0nbfvbi.mm"
include "df-aov.mm"
include "eleq1i.mm"
include "df-ov.mm"
include "3bitr4g.mm"

theorem aov0nbovbi
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (/) e/ C -> ( (( A F B )) e. C <-> ( A F B ) e. C ) )

  proof
    c0
    cC
    wnel
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cC
    wcel
    @0
    cF
    cfv
    #
    cC
    wcel
    cA
    cB
    cF
    caov
    #
    cC
    wcel
    cA
    cB
    cF
    co
    #
    cC
    wcel
    @0
    cC
    cF
    afv0nbfvbi
    @3
    @1
    cC
    cA
    cB
    cF
    df-aov
    eleq1i
    @4
    @2
    cC
    cA
    cB
    cF
    df-ov
    eleq1i
    3bitr4g
end
