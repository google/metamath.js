include "clc.mm"
include "wcel.mm"
include "clat.mm"
include "cpo.mm"
include "cvllat.mm"
include "latpos.mm"
include "syl.mm"

theorem cvlposN
  let cK: class K


  assert |- ( K e. CvLat -> K e. Poset )

  proof
    cK
    clc
    wcel
    cK
    clat
    wcel
    cK
    cpo
    wcel
    cK
    cvllat
    cK
    latpos
    syl
end
