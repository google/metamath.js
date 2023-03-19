include "ctsr.mm"
include "wcel.mm"
include "cps.mm"
include "cdm.mm"
include "cxp.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "eqid.mm"
include "istsr.mm"
include "simplbi.mm"

theorem tsrps
  let cR: class R


  assert |- ( R e. TosetRel -> R e. PosetRel )

  proof
    cR
    ctsr
    wcel
    cR
    cps
    wcel
    cR
    cdm
    #
    @0
    cxp
    cR
    cR
    ccnv
    cun
    wss
    cR
    @0
    @0
    eqid
    istsr
    simplbi
end
