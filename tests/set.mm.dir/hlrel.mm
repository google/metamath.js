include "chlo.mm"
include "ccbn.mm"
include "wss.mm"
include "wrel.mm"
include "cv.mm"
include "hlobn.mm"
include "ssriv.mm"
include "bnrel.mm"
include "relss.mm"
include "mp2.mm"

theorem hlrel
  let vx: setvar x


  assert |- Rel CHilOLD

  proof
    chlo
    ccbn
    wss
    ccbn
    wrel
    chlo
    wrel
    vx
    chlo
    ccbn
    vx
    cv
    hlobn
    ssriv
    bnrel
    chlo
    ccbn
    relss
    mp2
end
