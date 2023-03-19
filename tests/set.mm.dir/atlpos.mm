include "cal.mm"
include "wcel.mm"
include "clat.mm"
include "cpo.mm"
include "atllat.mm"
include "latpos.mm"
include "syl.mm"

theorem atlpos
  let cK: class K
  let vp: setvar p
  let vx: setvar x


  assert |- ( K e. AtLat -> K e. Poset )

  proof
    cK
    cal
    wcel
    cK
    clat
    wcel
    cK
    cpo
    wcel
    cK
    atllat
    cK
    latpos
    syl
end
