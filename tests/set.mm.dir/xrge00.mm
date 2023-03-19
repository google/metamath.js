include "cxrs.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "cmnd.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wss.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "xrs1mnd.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "cmnmnd.mm"
include "ax-mp.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "mnflt0.mm"
include "wb.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltnle.mm"
include "mp2an.mm"
include "mpbi.mm"
include "intnan.mm"
include "elxrge0.mm"
include "mtbir.mm"
include "difsn.mm"
include "iccssxr.mm"
include "ssdif.mm"
include "eqsstr3i.mm"
include "0e0iccpnf.mm"
include "cin.mm"
include "cbs.mm"
include "difss.mm"
include "df-ss.mm"
include "cvv.mm"
include "xrex.mm"
include "difexg.mm"
include "xrsbas.mm"
include "ressbas.mm"
include "eqtr3i.mm"
include "xrs10.mm"
include "ovex.mm"
include "ressress.mm"
include "dfss.mm"
include "incom.mm"
include "eqtr2i.mm"
include "oveq2i.mm"
include "submnd0.mm"
include "mp4an.mm"

theorem xrge00



  assert |- 0 = ( 0g ` ( RR*s |`s ( 0 [,] +oo ) ) )

  proof
    cxrs
    cxr
    cmnf
    csn
    #
    cdif
    #
    cress
    co
    #
    cmnd
    wcel
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    cmnd
    wcel
    #
    @3
    @1
    wss
    #
    cc0
    @3
    wcel
    cc0
    @4
    c0g
    cfv
    wceq
    @2
    @2
    eqid
    #
    xrs1mnd
    @4
    ccmn
    wcel
    @5
    xrge0cmn
    @4
    cmnmnd
    ax-mp
    @3
    @3
    @0
    cdif
    #
    @1
    cmnf
    @3
    wcel
    #
    wn
    @8
    @3
    wceq
    @9
    cmnf
    cxr
    wcel
    #
    cc0
    cmnf
    cle
    wbr
    #
    wa
    @11
    @10
    cmnf
    cc0
    clt
    wbr
    #
    @11
    wn
    #
    mnflt0
    @10
    cc0
    cxr
    wcel
    @12
    @13
    wb
    mnfxr
    0xr
    cmnf
    cc0
    xrltnle
    mp2an
    mpbi
    intnan
    cmnf
    elxrge0
    mtbir
    cmnf
    @3
    difsn
    ax-mp
    @3
    cxr
    wss
    @8
    @1
    wss
    cc0
    cpnf
    iccssxr
    @3
    cxr
    @0
    ssdif
    ax-mp
    eqsstr3i
    #
    0e0iccpnf
    @1
    @3
    @2
    @4
    cc0
    @1
    cxr
    cin
    #
    @1
    @2
    cbs
    cfv
    #
    @1
    cxr
    wss
    @15
    @1
    wceq
    cxr
    @0
    difss
    @1
    cxr
    df-ss
    mpbi
    @1
    cvv
    wcel
    #
    @15
    @16
    wceq
    cxr
    cvv
    wcel
    @17
    xrex
    cxr
    @0
    cvv
    difexg
    ax-mp
    #
    @1
    cxr
    @2
    cvv
    cxrs
    @7
    xrsbas
    ressbas
    ax-mp
    eqtr3i
    @2
    @7
    xrs10
    @2
    @3
    cress
    co
    #
    cxrs
    @1
    @3
    cin
    #
    cress
    co
    #
    @4
    @17
    @3
    cvv
    wcel
    @19
    @21
    wceq
    @18
    cc0
    cpnf
    cicc
    ovex
    @1
    @3
    cxrs
    cvv
    cvv
    ressress
    mp2an
    @20
    @3
    cxrs
    cress
    @3
    @3
    @1
    cin
    #
    @20
    @6
    @3
    @22
    wceq
    @14
    @3
    @1
    dfss
    mpbi
    @3
    @1
    incom
    eqtr2i
    oveq2i
    eqtr2i
    submnd0
    mp4an
end
