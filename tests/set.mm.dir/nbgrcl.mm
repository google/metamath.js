include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "csb.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "df-nbgr.mm"
include "mpt2xeldm.mm"
include "csbfv.mm"
include "eqtr4i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simpl2im.mm"

theorem nbgrcl
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vg: setvar g
  let ve: setvar e
  let vn: setvar n
  let vv: setvar v
  assume nbgrcl.v: |- V = ( Vtx ` G )


  assert |- ( N e. ( G NeighbVtx X ) -> X e. V )

  proof
    cN
    cG
    cX
    cnbgr
    co
    wcel
    cG
    cvv
    wcel
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
    wcel
    #
    cX
    cV
    wcel
    #
    vg
    vv
    cvv
    @1
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
    @0
    cedg
    cfv
    wrex
    vn
    @1
    @5
    csn
    cdif
    crab
    cnbgr
    cN
    cG
    cX
    vv
    ve
    vg
    vn
    df-nbgr
    mpt2xeldm
    @3
    @4
    @2
    cV
    cX
    @2
    cG
    cvtx
    cfv
    cV
    vg
    cG
    cvtx
    csbfv
    nbgrcl.v
    eqtr4i
    eleq2i
    biimpi
    simpl2im
end
