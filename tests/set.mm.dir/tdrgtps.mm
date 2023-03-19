include "ctdrg.mm"
include "wcel.mm"
include "ctrg.mm"
include "ctps.mm"
include "tdrgtrg.mm"
include "trgtps.mm"
include "syl.mm"

theorem tdrgtps
  let cR: class R


  assert |- ( R e. TopDRing -> R e. TopSp )

  proof
    cR
    ctdrg
    wcel
    cR
    ctrg
    wcel
    cR
    ctps
    wcel
    cR
    tdrgtrg
    cR
    trgtps
    syl
end
