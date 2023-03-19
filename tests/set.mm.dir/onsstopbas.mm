include "con0.mm"
include "ctb.mm"
include "cv.mm"
include "ontopbas.mm"
include "ssriv.mm"

theorem onsstopbas
  let vx: setvar x


  assert |- On C_ TopBases

  proof
    vx
    con0
    ctb
    vx
    cv
    ontopbas
    ssriv
end
