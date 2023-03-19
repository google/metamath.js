include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cr.mm"
include "recl.mm"
include "ax-mp.mm"

theorem recli
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( Re ` A ) e. RR

  proof
    cA
    cc
    wcel
    cA
    cre
    cfv
    cr
    wcel
    recl.1
    cA
    recl
    ax-mp
end
