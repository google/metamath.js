include "cdm.mm"
include "wcel.mm"
include "cafv.mm"
include "wn.mm"
include "cvv.mm"
include "wceq.mm"
include "ndmafv.mm"
include "nvelim.mm"
include "syl.mm"
include "con4i.mm"

theorem afvvdm
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) e. B -> A e. dom F )

  proof
    cA
    cF
    cdm
    wcel
    #
    cA
    cF
    cafv
    #
    cB
    wcel
    #
    @0
    wn
    @1
    cvv
    wceq
    @2
    wn
    cA
    cF
    ndmafv
    @1
    cB
    nvelim
    syl
    con4i
end
