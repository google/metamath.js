include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "ciedg.mm"
include "cdm.mm"
include "wfo.mm"
include "eqid.mm"
include "iseupth.mm"
include "simplbi.mm"

theorem eupthistrl
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( EulerPaths ` G ) P -> F ( Trails ` G ) P )

  proof
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    cfzo
    co
    cG
    ciedg
    cfv
    #
    cdm
    cF
    wfo
    cP
    cF
    cG
    @0
    @0
    eqid
    iseupth
    simplbi
end
