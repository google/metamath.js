include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "cui.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "eqid.mm"
include "isdrng.mm"
include "simplbi.mm"

theorem drngring
  let cR: class R


  assert |- ( R e. DivRing -> R e. Ring )

  proof
    cR
    cdr
    wcel
    cR
    crg
    wcel
    cR
    cui
    cfv
    #
    cR
    cbs
    cfv
    #
    cR
    c0g
    cfv
    #
    csn
    cdif
    wceq
    @1
    cR
    @0
    @2
    @1
    eqid
    @0
    eqid
    @2
    eqid
    isdrng
    simplbi
end
