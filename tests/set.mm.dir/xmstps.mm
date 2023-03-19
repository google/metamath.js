include "cxme.mm"
include "wcel.mm"
include "ctps.mm"
include "ctopn.mm"
include "cfv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wceq.mm"
include "eqid.mm"
include "isxms.mm"
include "simplbi.mm"

theorem xmstps
  let cM: class M


  assert |- ( M e. *MetSp -> M e. TopSp )

  proof
    cM
    cxme
    wcel
    cM
    ctps
    wcel
    cM
    ctopn
    cfv
    #
    cM
    cds
    cfv
    cM
    cbs
    cfv
    #
    @1
    cxp
    cres
    #
    cmopn
    cfv
    wceq
    @2
    @0
    cM
    @1
    @0
    eqid
    @1
    eqid
    @2
    eqid
    isxms
    simplbi
end
