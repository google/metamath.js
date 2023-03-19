include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cim.mm"
include "cneg.mm"
include "wceq.mm"
include "imcj.mm"
include "ax-mp.mm"

theorem imcji
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( Im ` ( * ` A ) ) = -u ( Im ` A )

  proof
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cim
    cfv
    cA
    cim
    cfv
    cneg
    wceq
    recl.1
    cA
    imcj
    ax-mp
end
