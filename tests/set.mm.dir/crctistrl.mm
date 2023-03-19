include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "crctprop.mm"
include "simpld.mm"

theorem crctistrl
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Circuits ` G ) P -> F ( Trails ` G ) P )

  proof
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cc0
    cP
    cfv
    cF
    chash
    cfv
    cP
    cfv
    wceq
    cP
    cF
    cG
    crctprop
    simpld
end
