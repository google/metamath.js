include "cnrg.mm"
include "wcel.mm"
include "cnm.mm"
include "cfv.mm"
include "cabv.mm"
include "crg.mm"
include "eqid.mm"
include "nrgabv.mm"
include "abvrcl.mm"
include "syl.mm"

theorem nrgring
  let cR: class R


  assert |- ( R e. NrmRing -> R e. Ring )

  proof
    cR
    cnrg
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
    cR
    crg
    wcel
    @1
    cR
    @0
    @0
    eqid
    @1
    eqid
    #
    nrgabv
    @1
    cR
    @0
    @2
    abvrcl
    syl
end
