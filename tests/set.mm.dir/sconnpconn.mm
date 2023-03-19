include "csconn.mm"
include "wcel.mm"
include "cpconn.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cicc.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "wi.mm"
include "cii.mm"
include "ccn.mm"
include "wral.mm"
include "issconn.mm"
include "simplbi.mm"

theorem sconnpconn
  let cJ: class J
  let cF: class F
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- ( J e. SConn -> J e. PConn )

  proof
    cJ
    csconn
    wcel
    cJ
    cpconn
    wcel
    cc0
    vf
    cv
    #
    cfv
    #
    c1
    @0
    cfv
    wceq
    @0
    cc0
    c1
    cicc
    co
    @1
    csn
    cxp
    cJ
    cphtpc
    cfv
    wbr
    wi
    vf
    cii
    cJ
    ccn
    co
    wral
    vf
    cJ
    issconn
    simplbi
end
