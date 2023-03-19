include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "trclfv.mm"
include "trclubg.mm"
include "eqsstrd.mm"

theorem trclfvub
  let cR: class R
  let cV: class V
  let vr: setvar r


  assert |- ( R e. V -> ( t+ ` R ) C_ ( R u. ( dom R X. ran R ) ) )

  proof
    cR
    cV
    wcel
    cR
    ctcl
    cfv
    cR
    vr
    cv
    #
    wss
    @0
    @0
    ccom
    @0
    wss
    wa
    vr
    cab
    cint
    cR
    cR
    cdm
    cR
    crn
    cxp
    cun
    vr
    cR
    cV
    trclfv
    cR
    cV
    vr
    trclubg
    eqsstrd
end
