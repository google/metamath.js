include "cz.mm"
include "cq.mm"
include "cv.mm"
include "zq.mm"
include "ssriv.mm"

theorem zssq
  let vx: setvar x


  assert |- ZZ C_ QQ

  proof
    vx
    cz
    cq
    vx
    cv
    zq
    ssriv
end
