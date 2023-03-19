include "c1.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "csgn.mm"
include "cfv.mm"
include "wceq.mm"
include "1re.mm"
include "rexri.mm"
include "0lt1.mm"
include "sgnp.mm"
include "mp2an.mm"

theorem sgn1



  assert |- ( sgn ` 1 ) = 1

  proof
    c1
    cxr
    wcel
    cc0
    c1
    clt
    wbr
    c1
    csgn
    cfv
    c1
    wceq
    c1
    1re
    rexri
    0lt1
    c1
    sgnp
    mp2an
end
