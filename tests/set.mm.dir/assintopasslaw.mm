include "cassintop.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "casslaw.mm"
include "wbr.mm"
include "assintop.mm"
include "simprd.mm"

theorem assintopasslaw
  let cM: class M
  let c.op: class .o.
  let vk: setvar k
  let vx: setvar x


  assert |- ( .o. e. ( assIntOp ` M ) -> .o. assLaw M )

  proof
    c.op
    cM
    cassintop
    cfv
    wcel
    cM
    cM
    cxp
    cM
    c.op
    wf
    c.op
    cM
    casslaw
    wbr
    cM
    c.op
    assintop
    simprd
end
