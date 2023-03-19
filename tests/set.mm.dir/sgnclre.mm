include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "csgn.mm"
include "cfv.mm"
include "wss.mm"
include "neg1rr.mm"
include "0re.mm"
include "1re.mm"
include "tpssi.mm"
include "mp3an.mm"
include "cxr.mm"
include "rexr.mm"
include "sgncl.mm"
include "syl.mm"
include "sseldi.mm"

theorem sgnclre
  let cA: class A


  assert |- ( A e. RR -> ( sgn ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    cr
    cA
    csgn
    cfv
    #
    @1
    cr
    wcel
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @2
    cr
    wss
    neg1rr
    0re
    1re
    @1
    cc0
    c1
    cr
    tpssi
    mp3an
    @0
    cA
    cxr
    wcel
    @3
    @2
    wcel
    cA
    rexr
    cA
    sgncl
    syl
    sseldi
end
