include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjcj.mm"
include "ax-mp.mm"

theorem cjcji
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( * ` ( * ` A ) ) = A

  proof
    cA
    cc
    wcel
    cA
    ccj
    cfv
    ccj
    cfv
    cA
    wceq
    recl.1
    cA
    cjcj
    ax-mp
end
