include "cz.mm"
include "cr.mm"
include "cv.mm"
include "zre.mm"
include "ssriv.mm"

theorem zssre
  let vx: setvar x


  assert |- ZZ C_ RR

  proof
    vx
    cz
    cr
    vx
    cv
    zre
    ssriv
end
