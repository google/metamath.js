include "cedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "wn.mm"
include "cvtx.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "rzal.mm"
include "ralnex.mm"
include "sylib.mm"
include "ralrimivw.mm"
include "nbgr0vtxlem.mm"

theorem nbgr0edg
  let cG: class G
  let cK: class K
  let ve: setvar e
  let vn: setvar n


  assert |- ( ( Edg ` G ) = (/) -> ( G NeighbVtx K ) = (/) )

  proof
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    ve
    vn
    cG
    cK
    @1
    cK
    vn
    cv
    cpr
    ve
    cv
    wss
    #
    ve
    @0
    wrex
    wn
    #
    vn
    cG
    cvtx
    cfv
    cK
    csn
    cdif
    @1
    @2
    wn
    #
    ve
    @0
    wral
    @3
    @4
    ve
    @0
    rzal
    @2
    ve
    @0
    ralnex
    sylib
    ralrimivw
    nbgr0vtxlem
end
