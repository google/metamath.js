include "ctrg.mm"
include "wcel.mm"
include "ctgp.mm"
include "crg.mm"
include "cmgp.mm"
include "cfv.mm"
include "ctmd.mm"
include "eqid.mm"
include "istrg.mm"
include "simp1bi.mm"

theorem trgtgp
  let cR: class R


  assert |- ( R e. TopRing -> R e. TopGrp )

  proof
    cR
    ctrg
    wcel
    cR
    ctgp
    wcel
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    #
    ctmd
    wcel
    cR
    @0
    @0
    eqid
    istrg
    simp1bi
end
