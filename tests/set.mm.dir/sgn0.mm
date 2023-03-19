include "cc0.mm"
include "csgn.mm"
include "cfv.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "sgnval.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iftruei.mm"
include "eqtri.mm"

theorem sgn0



  assert |- ( sgn ` 0 ) = 0

  proof
    cc0
    csgn
    cfv
    #
    cc0
    cc0
    wceq
    #
    cc0
    cc0
    cc0
    clt
    wbr
    c1
    cneg
    c1
    cif
    #
    cif
    #
    cc0
    cc0
    cxr
    wcel
    @0
    @3
    wceq
    0xr
    cc0
    sgnval
    ax-mp
    @1
    cc0
    @2
    cc0
    eqid
    iftruei
    eqtri
end
