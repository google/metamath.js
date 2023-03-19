include "cop.mm"
include "wdfat.mm"
include "cafv.mm"
include "cfv.mm"
include "caov.mm"
include "co.mm"
include "afvfundmfveq.mm"
include "df-aov.mm"
include "df-ov.mm"
include "3eqtr4g.mm"

theorem aovfundmoveq
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( F defAt <. A , B >. -> (( A F B )) = ( A F B ) )

  proof
    cA
    cB
    cop
    #
    cF
    wdfat
    @0
    cF
    cafv
    @0
    cF
    cfv
    cA
    cB
    cF
    caov
    cA
    cB
    cF
    co
    @0
    cF
    afvfundmfveq
    cA
    cB
    cF
    df-aov
    cA
    cB
    cF
    df-ov
    3eqtr4g
end
