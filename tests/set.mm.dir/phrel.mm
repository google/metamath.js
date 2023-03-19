include "ccphlo.mm"
include "cnv.mm"
include "wss.mm"
include "wrel.mm"
include "cv.mm"
include "phnv.mm"
include "ssriv.mm"
include "nvrel.mm"
include "relss.mm"
include "mp2.mm"

theorem phrel
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y


  assert |- Rel CPreHilOLD

  proof
    ccphlo
    cnv
    wss
    cnv
    wrel
    ccphlo
    wrel
    vx
    ccphlo
    cnv
    vx
    cv
    phnv
    ssriv
    nvrel
    ccphlo
    cnv
    relss
    mp2
end
