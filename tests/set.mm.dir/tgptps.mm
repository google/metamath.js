include "ctgp.mm"
include "wcel.mm"
include "ctmd.mm"
include "ctps.mm"
include "tgptmd.mm"
include "tmdtps.mm"
include "syl.mm"

theorem tgptps
  let cG: class G


  assert |- ( G e. TopGrp -> G e. TopSp )

  proof
    cG
    ctgp
    wcel
    cG
    ctmd
    wcel
    cG
    ctps
    wcel
    cG
    tgptmd
    cG
    tmdtps
    syl
end
