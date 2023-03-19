include "ctrg.mm"
include "wcel.mm"
include "ctgp.mm"
include "ctps.mm"
include "trgtgp.mm"
include "tgptps.mm"
include "syl.mm"

theorem trgtps
  let cR: class R


  assert |- ( R e. TopRing -> R e. TopSp )

  proof
    cR
    ctrg
    wcel
    cR
    ctgp
    wcel
    cR
    ctps
    wcel
    cR
    trgtgp
    cR
    tgptps
    syl
end
