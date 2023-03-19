include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "cxp.mm"
include "wfo.mm"
include "grpmnd.mm"
include "mndpfo.mm"
include "syl.mm"

theorem grpplusfo
  let cB: class B
  let cF: class F
  let cG: class G
  assume grpplusf.1: |- B = ( Base ` G )
  assume grpplusf.2: |- F = ( +f ` G )


  assert |- ( G e. Grp -> F : ( B X. B ) -onto-> B )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    cB
    cB
    cxp
    cB
    cF
    wfo
    cG
    grpmnd
    cB
    cF
    cG
    grpplusf.1
    grpplusf.2
    mndpfo
    syl
end
