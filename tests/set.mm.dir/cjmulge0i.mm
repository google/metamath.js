include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cjmulge0.mm"
include "ax-mp.mm"

theorem cjmulge0i
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- 0 <_ ( A x. ( * ` A ) )

  proof
    cA
    cc
    wcel
    cc0
    cA
    cA
    ccj
    cfv
    cmul
    co
    cle
    wbr
    recl.1
    cA
    cjmulge0
    ax-mp
end
