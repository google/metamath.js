include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "zre.mm"
include "leidd.mm"
include "ancli.mm"
include "eluz1.mm"
include "mpbird.mm"

theorem uzid
  let cM: class M


  assert |- ( M e. ZZ -> M e. ( ZZ>= ` M ) )

  proof
    cM
    cz
    wcel
    #
    cM
    cM
    cuz
    cfv
    wcel
    @0
    cM
    cM
    cle
    wbr
    #
    wa
    @0
    @1
    @0
    cM
    cM
    zre
    leidd
    ancli
    cM
    cM
    eluz1
    mpbird
end
