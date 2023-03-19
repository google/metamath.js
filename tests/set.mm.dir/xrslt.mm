include "clt.mm"
include "cle.mm"
include "cid.mm"
include "cdif.mm"
include "cxrs.mm"
include "cplt.mm"
include "cfv.mm"
include "dflt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "xrsex.mm"
include "xrsle.mm"
include "eqid.mm"
include "pltfval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem xrslt



  assert |- < = ( lt ` RR*s )

  proof
    clt
    cle
    cid
    cdif
    #
    cxrs
    cplt
    cfv
    #
    dflt2
    cxrs
    cvv
    wcel
    @1
    @0
    wceq
    xrsex
    cvv
    @1
    cxrs
    cle
    xrsle
    @1
    eqid
    pltfval
    ax-mp
    eqtr4i
end
