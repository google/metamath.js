include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cin.mm"
include "cxrs.mm"
include "cress.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "iccssxr.mm"
include "df-ss.mm"
include "mpbi.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "eqid.mm"
include "xrsbas.mm"
include "ressbas.mm"
include "ax-mp.mm"
include "eqtr3i.mm"

theorem xrge0base



  assert |- ( 0 [,] +oo ) = ( Base ` ( RR*s |`s ( 0 [,] +oo ) ) )

  proof
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cin
    #
    @0
    cxrs
    @0
    cress
    co
    #
    cbs
    cfv
    #
    @0
    cxr
    wss
    @1
    @0
    wceq
    cc0
    cpnf
    iccssxr
    @0
    cxr
    df-ss
    mpbi
    @0
    cvv
    wcel
    @1
    @3
    wceq
    cc0
    cpnf
    cicc
    ovex
    @0
    cxr
    @2
    cvv
    cxrs
    @2
    eqid
    xrsbas
    ressbas
    ax-mp
    eqtr3i
end
