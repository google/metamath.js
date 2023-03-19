include "cvv.mm"
include "wcel.mm"
include "cassintop.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "casslaw.mm"
include "wbr.mm"
include "wa.mm"
include "elfvex.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "assintopmap.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "elmapi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem assintop
  let cM: class M
  let c.op: class .o.
  let vo: setvar o
  let vk: setvar k
  let vx: setvar x


  assert |- ( .o. e. ( assIntOp ` M ) -> ( .o. : ( M X. M ) --> M /\ .o. assLaw M ) )

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
    cM
    cM
    cxp
    #
    cM
    c.op
    wf
    #
    c.op
    cM
    casslaw
    wbr
    #
    wa
    #
    c.op
    cM
    cassintop
    elfvex
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
    cM
    @3
    cmap
    co
    #
    crab
    #
    wcel
    #
    @6
    @0
    @1
    @10
    c.op
    vo
    cM
    cvv
    assintopmap
    eleq2d
    @11
    c.op
    @9
    wcel
    #
    @5
    wa
    @6
    @8
    @5
    vo
    c.op
    @9
    @7
    c.op
    cM
    casslaw
    breq1
    elrab
    @12
    @4
    @5
    c.op
    cM
    @3
    elmapi
    anim1i
    sylbi
    syl6bi
    mpcom
end
