include "cq.mm"
include "cr.mm"
include "cv.mm"
include "qre.mm"
include "ssriv.mm"

theorem qssre
  let vx: setvar x


  assert |- QQ C_ RR

  proof
    vx
    cq
    cr
    vx
    cv
    qre
    ssriv
end
