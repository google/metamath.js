include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cvv.mm"
include "elfvdm.mm"
include "elex.mm"
include "syl.mm"

theorem elfvex
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A e. ( F ` B ) -> B e. _V )

  proof
    cA
    cB
    cF
    cfv
    wcel
    cB
    cF
    cdm
    #
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cF
    elfvdm
    cB
    @0
    elex
    syl
end
