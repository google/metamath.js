include "c0.mm"
include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "f10.mm"
include "wb.mm"
include "dm0.mm"
include "f1eq2.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "cvv.mm"
include "0ex.mm"
include "cvtx.mm"
include "vtxval0.mm"
include "eqcomi.mm"
include "ciedg.mm"
include "iedgval0.mm"
include "isusgr.mm"

theorem usgr0
  let vx: setvar x


  assert |- (/) e. USGraph

  proof
    c0
    cusgr
    wcel
    #
    c0
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    c0
    cpw
    c0
    csn
    cdif
    crab
    #
    c0
    wf1
    #
    @3
    c0
    @2
    c0
    wf1
    #
    @2
    f10
    @1
    c0
    wceq
    @3
    @4
    wb
    dm0
    @1
    c0
    @2
    c0
    f1eq2
    ax-mp
    mpbir
    c0
    cvv
    wcel
    @0
    @3
    wb
    0ex
    vx
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
    isusgr
    ax-mp
    mpbir
end
