include "c0.mm"
include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "f0.mm"
include "dm0.mm"
include "pw0.mm"
include "difeq1i.mm"
include "difid.mm"
include "eqtri.mm"
include "feq23i.mm"
include "mpbir.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "cvtx.mm"
include "cfv.mm"
include "vtxval0.mm"
include "eqcomi.mm"
include "ciedg.mm"
include "iedgval0.mm"
include "isuhgr.mm"
include "ax-mp.mm"

theorem uhgr0



  assert |- (/) e. UHGraph

  proof
    c0
    cuhgr
    wcel
    #
    c0
    cdm
    #
    c0
    cpw
    #
    c0
    csn
    #
    cdif
    #
    c0
    wf
    #
    @5
    c0
    c0
    c0
    wf
    c0
    f0
    @1
    @4
    c0
    c0
    c0
    dm0
    @4
    @3
    @3
    cdif
    c0
    @2
    @3
    @3
    pw0
    difeq1i
    @3
    difid
    eqtri
    feq23i
    mpbir
    c0
    cvv
    wcel
    @0
    @5
    wb
    0ex
    cvv
    c0
    c0
    c0
    c0
    cvtx
    cfv
    c0
    vtxval0
    eqcomi
    c0
    ciedg
    cfv
    c0
    iedgval0
    eqcomi
    isuhgr
    ax-mp
    mpbir
end
