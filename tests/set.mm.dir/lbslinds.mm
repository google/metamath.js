include "clinds.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "clspn.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "islbs4.mm"
include "simplbi.mm"
include "ssriv.mm"

theorem lbslinds
  let cJ: class J
  let cW: class W
  let va: setvar a
  assume lbslinds.j: |- J = ( LBasis ` W )


  assert |- J C_ ( LIndS ` W )

  proof
    va
    cJ
    cW
    clinds
    cfv
    #
    va
    cv
    #
    cJ
    wcel
    @1
    @0
    wcel
    @1
    cW
    clspn
    cfv
    #
    cfv
    cW
    cbs
    cfv
    #
    wceq
    @3
    cJ
    @2
    cW
    @1
    @3
    eqid
    lbslinds.j
    @2
    eqid
    islbs4
    simplbi
    ssriv
end
