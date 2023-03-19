include "cnrg.mm"
include "wcel.mm"
include "cngp.mm"
include "cabl.mm"
include "ctgp.mm"
include "nrgngp.mm"
include "crg.mm"
include "nrgring.mm"
include "ringabl.mm"
include "syl.mm"
include "ngptgp.mm"
include "syl2anc.mm"

theorem nrgtgp
  let cR: class R


  assert |- ( R e. NrmRing -> R e. TopGrp )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cngp
    wcel
    cR
    cabl
    wcel
    #
    cR
    ctgp
    wcel
    cR
    nrgngp
    @0
    cR
    crg
    wcel
    @1
    cR
    nrgring
    cR
    ringabl
    syl
    cR
    ngptgp
    syl2anc
end
