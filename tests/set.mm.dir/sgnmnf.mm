include "cmnf.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "mnfxr.mm"
include "mnflt0.mm"
include "sgnn.mm"
include "mp2an.mm"

theorem sgnmnf



  assert |- ( sgn ` -oo ) = -u 1

  proof
    cmnf
    cxr
    wcel
    cmnf
    cc0
    clt
    wbr
    cmnf
    csgn
    cfv
    c1
    cneg
    wceq
    mnfxr
    mnflt0
    cmnf
    sgnn
    mp2an
end
