include "ctrg.mm"
include "wcel.mm"
include "ctgp.mm"
include "ctmd.mm"
include "trgtgp.mm"
include "tgptmd.mm"
include "syl.mm"

theorem trgtmd2
  let cR: class R


  assert |- ( R e. TopRing -> R e. TopMnd )

  proof
    cR
    ctrg
    wcel
    cR
    ctgp
    wcel
    cR
    ctmd
    wcel
    cR
    trgtgp
    cR
    tgptmd
    syl
end
