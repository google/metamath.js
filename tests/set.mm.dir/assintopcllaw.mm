include "cvv.mm"
include "wcel.mm"
include "cassintop.mm"
include "cfv.mm"
include "ccllaw.mm"
include "wbr.mm"
include "elfvex.mm"
include "cclintop.mm"
include "casslaw.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "assintopval.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"
include "clintopcllaw.mm"
include "adantr.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem assintopcllaw
  let cM: class M
  let c.op: class .o.
  let vo: setvar o
  let vk: setvar k
  let vx: setvar x


  assert |- ( .o. e. ( assIntOp ` M ) -> .o. clLaw M )

  proof
    cM
    cvv
    wcel
    #
    c.op
    cM
    cassintop
    cfv
    #
    wcel
    #
    c.op
    cM
    ccllaw
    wbr
    #
    c.op
    cM
    cassintop
    elfvex
    @0
    @2
    c.op
    cM
    cclintop
    cfv
    #
    wcel
    #
    c.op
    cM
    casslaw
    wbr
    #
    wa
    #
    @3
    @0
    @2
    c.op
    vo
    cv
    #
    cM
    casslaw
    wbr
    #
    vo
    @4
    crab
    #
    wcel
    @7
    @0
    @1
    @10
    c.op
    vo
    cM
    cvv
    assintopval
    eleq2d
    @9
    @6
    vo
    c.op
    @4
    @8
    c.op
    cM
    casslaw
    breq1
    elrab
    syl6bb
    @5
    @3
    @6
    cM
    c.op
    clintopcllaw
    adantr
    syl6bi
    mpcom
end
