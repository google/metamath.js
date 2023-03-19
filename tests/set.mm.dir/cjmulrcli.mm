include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "cjmulrcl.mm"
include "ax-mp.mm"

theorem cjmulrcli
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( A x. ( * ` A ) ) e. RR

  proof
    cA
    cc
    wcel
    cA
    cA
    ccj
    cfv
    cmul
    co
    cr
    wcel
    recl.1
    cA
    cjmulrcl
    ax-mp
end
