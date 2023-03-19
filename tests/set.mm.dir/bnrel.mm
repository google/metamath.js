include "ccbn.mm"
include "cnv.mm"
include "wss.mm"
include "wrel.mm"
include "cv.mm"
include "bnnv.mm"
include "ssriv.mm"
include "nvrel.mm"
include "relss.mm"
include "mp2.mm"

theorem bnrel
  let vx: setvar x


  assert |- Rel CBan

  proof
    ccbn
    cnv
    wss
    cnv
    wrel
    ccbn
    wrel
    vx
    ccbn
    cnv
    vx
    cv
    bnnv
    ssriv
    nvrel
    ccbn
    cnv
    relss
    mp2
end
