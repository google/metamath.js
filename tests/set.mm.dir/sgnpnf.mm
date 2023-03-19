include "cpnf.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "pnfxr.mm"
include "0ltpnf.mm"
include "sgnp.mm"
include "mp2an.mm"

theorem sgnpnf



  assert |- ( sgn ` +oo ) = 1

  proof
    cpnf
    cxr
    wcel
    cc0
    cpnf
    clt
    wbr
    cpnf
    csgn
    cfv
    c1
    wceq
    pnfxr
    0ltpnf
    cpnf
    sgnp
    mp2an
end
