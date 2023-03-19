include "ctdrg.mm"
include "wcel.mm"
include "ctrg.mm"
include "crg.mm"
include "tdrgtrg.mm"
include "trgring.mm"
include "syl.mm"

theorem tdrgring
  let cR: class R


  assert |- ( R e. TopDRing -> R e. Ring )

  proof
    cR
    ctdrg
    wcel
    cR
    ctrg
    wcel
    cR
    crg
    wcel
    cR
    tdrgtrg
    cR
    trgring
    syl
end
