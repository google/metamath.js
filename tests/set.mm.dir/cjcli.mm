include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cjcl.mm"
include "ax-mp.mm"

theorem cjcli
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( * ` A ) e. CC

  proof
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cc
    wcel
    recl.1
    cA
    cjcl
    ax-mp
end
