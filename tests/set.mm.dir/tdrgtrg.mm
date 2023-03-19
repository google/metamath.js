include "ctdrg.mm"
include "wcel.mm"
include "ctrg.mm"
include "cdr.mm"
include "cmgp.mm"
include "cfv.mm"
include "cui.mm"
include "cress.mm"
include "co.mm"
include "ctgp.mm"
include "eqid.mm"
include "istdrg.mm"
include "simp1bi.mm"

theorem tdrgtrg
  let cR: class R


  assert |- ( R e. TopDRing -> R e. TopRing )

  proof
    cR
    ctdrg
    wcel
    cR
    ctrg
    wcel
    cR
    cdr
    wcel
    cR
    cmgp
    cfv
    #
    cR
    cui
    cfv
    #
    cress
    co
    ctgp
    wcel
    cR
    @1
    @0
    @0
    eqid
    @1
    eqid
    istdrg
    simp1bi
end
