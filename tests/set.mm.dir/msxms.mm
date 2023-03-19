include "cmt.mm"
include "wcel.mm"
include "cxme.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "ctopn.mm"
include "eqid.mm"
include "isms.mm"
include "simplbi.mm"

theorem msxms
  let cM: class M


  assert |- ( M e. MetSp -> M e. *MetSp )

  proof
    cM
    cmt
    wcel
    cM
    cxme
    wcel
    cM
    cds
    cfv
    cM
    cbs
    cfv
    #
    @0
    cxp
    cres
    #
    @0
    cme
    cfv
    wcel
    @1
    cM
    ctopn
    cfv
    #
    cM
    @0
    @2
    eqid
    @0
    eqid
    @1
    eqid
    isms
    simplbi
end
