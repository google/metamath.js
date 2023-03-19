include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cen.mm"
include "df-en.mm"
include "relopabi.mm"

theorem relen
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- Rel ~~

  proof
    vx
    cv
    vy
    cv
    vf
    cv
    wf1o
    vf
    wex
    vx
    vy
    cen
    vx
    vy
    vf
    df-en
    relopabi
end
