include "wnel.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "csb.mm"
include "wo.mm"
include "cnbgr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "csbfv.mm"
include "eqtr4i.mm"
include "neleq2.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "olcd.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "df-nbgr.mm"
include "mpt2xneldm.mm"
include "syl.mm"

theorem nbgrnvtx0
  let cG: class G
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vg: setvar g
  let vn: setvar n
  let vv: setvar v
  assume nbgrel.v: |- V = ( Vtx ` G )


  assert |- ( X e/ V -> ( G NeighbVtx X ) = (/) )

  proof
    cX
    cV
    wnel
    #
    cG
    cvv
    wnel
    #
    cX
    vg
    cG
    vg
    cv
    #
    cvtx
    cfv
    #
    csb
    #
    wnel
    #
    wo
    cG
    cX
    cnbgr
    co
    c0
    wceq
    @0
    @5
    @1
    @0
    @5
    cV
    @4
    wceq
    @0
    @5
    wb
    cV
    cG
    cvtx
    cfv
    @4
    nbgrel.v
    vg
    cG
    cvtx
    csbfv
    eqtr4i
    cV
    @4
    cX
    neleq2
    ax-mp
    biimpi
    olcd
    vg
    vv
    cvv
    @3
    vv
    cv
    #
    vn
    cv
    cpr
    ve
    cv
    wss
    ve
    @2
    cedg
    cfv
    wrex
    vn
    @3
    @6
    csn
    cdif
    crab
    cnbgr
    cG
    cX
    vv
    ve
    vg
    vn
    df-nbgr
    mpt2xneldm
    syl
end
