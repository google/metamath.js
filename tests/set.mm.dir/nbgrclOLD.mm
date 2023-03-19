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
include "eleq2i.mm"
include "biimpi.mm"
include "simpl2im.mm"

theorem nbgrclOLD
  let cG: class G
  let cN: class N
  let cX: class X
  let vg: setvar g
  let ve: setvar e
  let vn: setvar n
  let vv: setvar v


  assert |- ( N e. ( G NeighbVtx X ) -> X e. ( Vtx ` G ) )

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
    cG
    cvtx
    cfv
    #
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
    @6
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
    @5
    @2
    @4
    cX
    vg
    cG
    cvtx
    csbfv
    eleq2i
    biimpi
    simpl2im
end
