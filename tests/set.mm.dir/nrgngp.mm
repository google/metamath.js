include "cnrg.mm"
include "wcel.mm"
include "cngp.mm"
include "cnm.mm"
include "cfv.mm"
include "cabv.mm"
include "eqid.mm"
include "isnrg.mm"
include "simplbi.mm"

theorem nrgngp
  let cR: class R


  assert |- ( R e. NrmRing -> R e. NrmGrp )

  proof
    cR
    cnrg
    wcel
    cR
    cngp
    wcel
    cR
    cnm
    cfv
    #
    cR
    cabv
    cfv
    #
    wcel
    @1
    cR
    @0
    @0
    eqid
    @1
    eqid
    isnrg
    simplbi
end
