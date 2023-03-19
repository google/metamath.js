include "c2ndc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "ctop.mm"
include "is2ndc.mm"
include "simprr.mm"
include "tgcl.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "rexlimiva.mm"
include "sylbi.mm"

theorem 2ndctop
  let cJ: class J
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( J e. 2ndc -> J e. Top )

  proof
    cJ
    c2ndc
    wcel
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @0
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vx
    ctb
    wrex
    cJ
    ctop
    wcel
    #
    vx
    cJ
    is2ndc
    @4
    @5
    vx
    ctb
    @0
    ctb
    wcel
    #
    @4
    wa
    @2
    cJ
    ctop
    @6
    @1
    @3
    simprr
    @6
    @2
    ctop
    wcel
    @4
    @0
    tgcl
    adantr
    eqeltrrd
    rexlimiva
    sylbi
end
