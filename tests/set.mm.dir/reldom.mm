include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cdom.mm"
include "df-dom.mm"
include "relopabi.mm"

theorem reldom
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- Rel ~<_

  proof
    vx
    cv
    vy
    cv
    vf
    cv
    wf1
    vf
    wex
    vx
    vy
    cdom
    vx
    vy
    vf
    df-dom
    relopabi
end
