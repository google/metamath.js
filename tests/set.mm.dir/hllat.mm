include "chlt.mm"
include "wcel.mm"
include "cal.mm"
include "clat.mm"
include "hlatl.mm"
include "atllat.mm"
include "syl.mm"

theorem hllat
  let cK: class K


  assert |- ( K e. HL -> K e. Lat )

  proof
    cK
    chlt
    wcel
    cK
    cal
    wcel
    cK
    clat
    wcel
    cK
    hlatl
    cK
    atllat
    syl
end
