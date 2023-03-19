include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cdm.mm"
include "cafv.mm"
include "wceq.mm"
include "prcnel.mm"
include "ndmafv.mm"
include "syl.mm"

theorem afvprc
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. A e. _V -> ( F ''' A ) = _V )

  proof
    cA
    cvv
    wcel
    wn
    cA
    cF
    cdm
    #
    wcel
    wn
    cA
    cF
    cafv
    cvv
    wceq
    cA
    @0
    prcnel
    cA
    cF
    ndmafv
    syl
end
