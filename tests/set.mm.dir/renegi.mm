include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "reneg.mm"
include "ax-mp.mm"

theorem renegi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( Re ` -u A ) = -u ( Re ` A )

  proof
    cA
    cc
    wcel
    cA
    cneg
    cre
    cfv
    cA
    cre
    cfv
    cneg
    wceq
    recl.1
    cA
    reneg
    ax-mp
end
