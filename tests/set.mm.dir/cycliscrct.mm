include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "ctrls.mm"
include "ccycls.mm"
include "ccrcts.mm"
include "pthistrl.mm"
include "anim1i.mm"
include "iscycl.mm"
include "iscrct.mm"
include "3imtr4i.mm"

theorem cycliscrct
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Cycles ` G ) P -> F ( Circuits ` G ) P )

  proof
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cc0
    cP
    cfv
    cF
    chash
    cfv
    cP
    cfv
    wceq
    #
    wa
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    @1
    wa
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    @0
    @2
    @1
    cP
    cF
    cG
    pthistrl
    anim1i
    cP
    cF
    cG
    iscycl
    cP
    cF
    cG
    iscrct
    3imtr4i
end
