include "cnbgr.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "df-nbgr.mm"
include "reldmmpt2.mm"
include "ovprc.mm"

theorem nbgrprc0
  let cG: class G
  let cN: class N
  let ve: setvar e
  let vg: setvar g
  let vn: setvar n
  let vv: setvar v


  assert |- ( -. ( G e. _V /\ N e. _V ) -> ( G NeighbVtx N ) = (/) )

  proof
    cG
    cN
    cnbgr
    vg
    vv
    cvv
    vg
    cv
    #
    cvtx
    cfv
    #
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
    @2
    csn
    cdif
    crab
    cnbgr
    vv
    ve
    vg
    vn
    df-nbgr
    reldmmpt2
    ovprc
end
