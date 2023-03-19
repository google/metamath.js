include "cuhgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "csubgr.mm"
include "wbr.mm"
include "eqid.mm"
include "uhgrfun.mm"
include "subgrfun.mm"
include "sylan.mm"

theorem subgruhgrfun
  let cS: class S
  let cG: class G


  assert |- ( ( G e. UHGraph /\ S SubGraph G ) -> Fun ( iEdg ` S ) )

  proof
    cG
    cuhgr
    wcel
    cG
    ciedg
    cfv
    #
    wfun
    cS
    cG
    csubgr
    wbr
    cS
    ciedg
    cfv
    wfun
    @0
    cG
    @0
    eqid
    uhgrfun
    cS
    cG
    subgrfun
    sylan
end
