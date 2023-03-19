include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "0re.mm"
include "ltleii.mm"
include "sqrtcli.mm"
include "ax-mp.mm"

theorem sqrtpclii
  let cA: class A
  assume sqrth.1: |- A e. RR
  assume sqrpclii.2: |- 0 < A


  assert |- ( sqrt ` A ) e. RR

  proof
    cc0
    cA
    cle
    wbr
    cA
    csqrt
    cfv
    cr
    wcel
    cc0
    cA
    0re
    sqrth.1
    sqrpclii.2
    ltleii
    cA
    sqrth.1
    sqrtcli
    ax-mp
end
