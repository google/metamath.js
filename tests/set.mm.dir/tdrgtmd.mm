include "ctdrg.mm"
include "wcel.mm"
include "ctrg.mm"
include "ctmd.mm"
include "tdrgtrg.mm"
include "trgtmd2.mm"
include "syl.mm"

theorem tdrgtmd
  let cR: class R


  assert |- ( R e. TopDRing -> R e. TopMnd )

  proof
    cR
    ctdrg
    wcel
    cR
    ctrg
    wcel
    cR
    ctmd
    wcel
    cR
    tdrgtrg
    cR
    trgtmd2
    syl
end
