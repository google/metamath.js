include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "cxp.mm"
include "wf.mm"
include "grpmnd.mm"
include "mndplusf.mm"
include "syl.mm"

theorem grpplusf
  let cB: class B
  let cF: class F
  let cG: class G
  assume grpplusf.1: |- B = ( Base ` G )
  assume grpplusf.2: |- F = ( +f ` G )


  assert |- ( G e. Grp -> F : ( B X. B ) --> B )

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
    wf
    cG
    grpmnd
    cB
    cF
    cG
    grpplusf.1
    grpplusf.2
    mndplusf
    syl
end
