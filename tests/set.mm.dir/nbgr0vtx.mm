include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "ral0.mm"
include "difeq1.mm"
include "0dif.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "nbgr0vtxlem.mm"

theorem nbgr0vtx
  let cG: class G
  let cK: class K
  let ve: setvar e
  let vn: setvar n


  assert |- ( ( Vtx ` G ) = (/) -> ( G NeighbVtx K ) = (/) )

  proof
    cG
    cvtx
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
    ve
    cG
    cedg
    cfv
    wrex
    wn
    #
    vn
    @0
    cK
    csn
    #
    cdif
    #
    wral
    @2
    vn
    c0
    wral
    @2
    vn
    ral0
    @1
    @2
    vn
    @4
    c0
    @1
    @4
    c0
    @3
    cdif
    c0
    @0
    c0
    @3
    difeq1
    @3
    0dif
    syl6eq
    raleqdv
    mpbiri
    nbgr0vtxlem
end
