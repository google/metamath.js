include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "ccnv.mm"
include "wfun.mm"
include "istrl.mm"
include "simplbi.mm"

theorem trliswlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Trails ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    ccnv
    wfun
    cP
    cF
    cG
    istrl
    simplbi
end
