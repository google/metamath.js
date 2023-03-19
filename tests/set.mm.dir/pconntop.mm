include "cpconn.mm"
include "wcel.mm"
include "ctop.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "eqid.mm"
include "ispconn.mm"
include "simplbi.mm"

theorem pconntop
  let cJ: class J
  let cF: class F
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- ( J e. PConn -> J e. Top )

  proof
    cJ
    cpconn
    wcel
    cJ
    ctop
    wcel
    cc0
    vf
    cv
    #
    cfv
    vx
    cv
    wceq
    c1
    @0
    cfv
    vy
    cv
    wceq
    wa
    vf
    cii
    cJ
    ccn
    co
    wrex
    vy
    cJ
    cuni
    #
    wral
    vx
    @1
    wral
    vx
    vy
    vf
    cJ
    @1
    @1
    eqid
    ispconn
    simplbi
end
