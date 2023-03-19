include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cre.mm"
include "wceq.mm"
include "recj.mm"
include "ax-mp.mm"

theorem recji
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( Re ` ( * ` A ) ) = ( Re ` A )

  proof
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cre
    cfv
    cA
    cre
    cfv
    wceq
    recl.1
    cA
    recj
    ax-mp
end
