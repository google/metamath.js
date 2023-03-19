include "cvv.mm"
include "wcel.mm"
include "cclintop.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "elfvex.mm"
include "isclintop.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem clintop
  let cM: class M
  let c.op: class .o.
  let vk: setvar k
  let vx: setvar x


  assert |- ( .o. e. ( clIntOp ` M ) -> .o. : ( M X. M ) --> M )

  proof
    cM
    cvv
    wcel
    #
    c.op
    cM
    cclintop
    cfv
    wcel
    #
    cM
    cM
    cxp
    cM
    c.op
    wf
    #
    c.op
    cM
    cclintop
    elfvex
    @0
    @1
    @2
    cM
    cvv
    c.op
    isclintop
    biimpd
    mpcom
end
