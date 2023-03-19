include "cxrs.mm"
include "cp0.mm"
include "cfv.mm"
include "cxr.mm"
include "cglb.mm"
include "clt.mm"
include "cinf.mm"
include "cmnf.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "xrsex.mm"
include "xrsbas.mm"
include "eqid.mm"
include "p0val.mm"
include "ax-mp.mm"
include "wss.mm"
include "ssid.mm"
include "xrslt.mm"
include "ctos.mm"
include "xrstos.mm"
include "a1i.mm"
include "id.mm"
include "tosglb.mm"
include "xrinfm.mm"
include "3eqtrri.mm"

theorem xrsp0



  assert |- -oo = ( 0. ` RR*s )

  proof
    cxrs
    cp0
    cfv
    #
    cxr
    cxrs
    cglb
    cfv
    #
    cfv
    #
    cxr
    cxr
    clt
    cinf
    #
    cmnf
    cxrs
    cvv
    wcel
    @0
    @2
    wceq
    xrsex
    cxr
    @1
    cxrs
    cvv
    @0
    xrsbas
    @1
    eqid
    @0
    eqid
    p0val
    ax-mp
    cxr
    cxr
    wss
    #
    @2
    @3
    wceq
    cxr
    ssid
    @4
    cxr
    cxr
    clt
    cxrs
    xrsbas
    xrslt
    cxrs
    ctos
    wcel
    @4
    xrstos
    a1i
    @4
    id
    tosglb
    ax-mp
    xrinfm
    3eqtrri
end
