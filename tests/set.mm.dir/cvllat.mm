include "clc.mm"
include "wcel.mm"
include "cal.mm"
include "clat.mm"
include "cvlatl.mm"
include "atllat.mm"
include "syl.mm"

theorem cvllat
  let cK: class K


  assert |- ( K e. CvLat -> K e. Lat )

  proof
    cK
    clc
    wcel
    cK
    cal
    wcel
    cK
    clat
    wcel
    cK
    cvlatl
    cK
    atllat
    syl
end
