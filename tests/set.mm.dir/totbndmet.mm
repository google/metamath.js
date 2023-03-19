include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cfn.mm"
include "crp.mm"
include "istotbnd.mm"
include "simplbi.mm"

theorem totbndmet
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vv: setvar v
  let vx: setvar x


  assert |- ( M e. ( TotBnd ` X ) -> M e. ( Met ` X ) )

  proof
    cM
    cX
    ctotbnd
    cfv
    wcel
    cM
    cX
    cme
    cfv
    wcel
    vv
    cv
    #
    cuni
    cX
    wceq
    vb
    cv
    vx
    cv
    vd
    cv
    cM
    cbl
    cfv
    co
    wceq
    vx
    cX
    wrex
    vb
    @0
    wral
    wa
    vv
    cfn
    wrex
    vd
    crp
    wral
    vx
    vv
    cM
    cX
    vb
    vd
    istotbnd
    simplbi
end
