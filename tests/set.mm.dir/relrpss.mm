include "cv.mm"
include "wpss.mm"
include "crpss.mm"
include "df-rpss.mm"
include "relopabi.mm"

theorem relrpss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- Rel [C.]

  proof
    vx
    cv
    vy
    cv
    wpss
    vx
    vy
    crpss
    vx
    vy
    df-rpss
    relopabi
end
