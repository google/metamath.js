include "crp.mm"
include "cr.mm"
include "cv.mm"
include "rpre.mm"
include "ssriv.mm"

theorem rpssre
  let vx: setvar x


  assert |- RR+ C_ RR

  proof
    vx
    crp
    cr
    vx
    cv
    rpre
    ssriv
end
