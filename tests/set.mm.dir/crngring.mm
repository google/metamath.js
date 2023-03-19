include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "eqid.mm"
include "iscrng.mm"
include "simplbi.mm"

theorem crngring
  let cR: class R


  assert |- ( R e. CRing -> R e. Ring )

  proof
    cR
    ccrg
    wcel
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    #
    ccmn
    wcel
    cR
    @0
    @0
    eqid
    iscrng
    simplbi
end
