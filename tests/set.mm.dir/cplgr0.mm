include "c0.mm"
include "ccplgr.mm"
include "wcel.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cvtx.mm"
include "wral.mm"
include "ral0.mm"
include "vtxval0.mm"
include "raleqi.mm"
include "mpbir.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "eqid.mm"
include "iscplgr.mm"
include "ax-mp.mm"

theorem cplgr0
  let vv: setvar v


  assert |- (/) e. ComplGraph

  proof
    c0
    ccplgr
    wcel
    #
    vv
    cv
    c0
    cuvtx
    cfv
    wcel
    #
    vv
    c0
    cvtx
    cfv
    #
    wral
    #
    @3
    @1
    vv
    c0
    wral
    @1
    vv
    ral0
    @1
    vv
    @2
    c0
    vtxval0
    raleqi
    mpbir
    c0
    cvv
    wcel
    @0
    @3
    wb
    0ex
    vv
    c0
    @2
    cvv
    @2
    eqid
    iscplgr
    ax-mp
    mpbir
end
