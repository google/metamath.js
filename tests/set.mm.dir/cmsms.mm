include "ccms.mm"
include "wcel.mm"
include "cmt.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cms.mm"
include "eqid.mm"
include "iscms.mm"
include "simplbi.mm"

theorem cmsms
  let cG: class G


  assert |- ( G e. CMetSp -> G e. MetSp )

  proof
    cG
    ccms
    wcel
    cG
    cmt
    wcel
    cG
    cds
    cfv
    cG
    cbs
    cfv
    #
    @0
    cxp
    cres
    #
    @0
    cms
    cfv
    wcel
    @1
    cG
    @0
    @0
    eqid
    @1
    eqid
    iscms
    simplbi
end
