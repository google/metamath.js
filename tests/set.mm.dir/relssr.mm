include "cv.mm"
include "wss.mm"
include "cssr.mm"
include "df-ssr.mm"
include "relopabi.mm"

theorem relssr
  let vx: setvar x
  let vy: setvar y


  assert |- Rel _S

  proof
    vx
    cv
    vy
    cv
    wss
    vx
    vy
    cssr
    vx
    vy
    df-ssr
    relopabi
end
