include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "ne0i.mm"
include "ndmfv.mm"
include "necon1ai.mm"
include "syl.mm"

theorem elfvdm
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A e. ( F ` B ) -> B e. dom F )

  proof
    cA
    cB
    cF
    cfv
    #
    wcel
    @0
    c0
    wne
    cB
    cF
    cdm
    wcel
    #
    @0
    cA
    ne0i
    @1
    @0
    c0
    cB
    cF
    ndmfv
    necon1ai
    syl
end
