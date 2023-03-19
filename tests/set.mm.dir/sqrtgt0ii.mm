include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "sqrtgt0i.mm"
include "ax-mp.mm"

theorem sqrtgt0ii
  let cA: class A
  assume sqrth.1: |- A e. RR
  assume sqrpclii.2: |- 0 < A


  assert |- 0 < ( sqrt ` A )

  proof
    cc0
    cA
    clt
    wbr
    cc0
    cA
    csqrt
    cfv
    clt
    wbr
    sqrpclii.2
    cA
    sqrth.1
    sqrtgt0i
    ax-mp
end
