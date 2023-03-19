include "cop.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "caov.mm"
include "cafv.mm"
include "cvv.mm"
include "df-aov.mm"
include "ndmafv.mm"
include "syl5eq.mm"

theorem ndmaov
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. <. A , B >. e. dom F -> (( A F B )) = _V )

  proof
    cA
    cB
    cop
    #
    cF
    cdm
    wcel
    wn
    cA
    cB
    cF
    caov
    @0
    cF
    cafv
    cvv
    cA
    cB
    cF
    df-aov
    @0
    cF
    ndmafv
    syl5eq
end
