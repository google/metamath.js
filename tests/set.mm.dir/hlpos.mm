include "chlt.mm"
include "wcel.mm"
include "clat.mm"
include "cpo.mm"
include "hllat.mm"
include "latpos.mm"
include "syl.mm"

theorem hlpos
  let cK: class K


  assert |- ( K e. HL -> K e. Poset )

  proof
    cK
    chlt
    wcel
    cK
    clat
    wcel
    cK
    cpo
    wcel
    cK
    hllat
    cK
    latpos
    syl
end
