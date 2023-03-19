include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cedg.mm"
include "cpw.mm"
include "w3a.mm"
include "csubgr.mm"
include "df-subgr.mm"
include "relopabi.mm"

theorem relsubgr
  let vg: setvar g
  let vs: setvar s


  assert |- Rel SubGraph

  proof
    vs
    cv
    #
    cvtx
    cfv
    #
    vg
    cv
    #
    cvtx
    cfv
    wss
    @0
    ciedg
    cfv
    #
    @2
    ciedg
    cfv
    @3
    cdm
    cres
    wceq
    @0
    cedg
    cfv
    @1
    cpw
    wss
    w3a
    vs
    vg
    csubgr
    vg
    vs
    df-subgr
    relopabi
end
