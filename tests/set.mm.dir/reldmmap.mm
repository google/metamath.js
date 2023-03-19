include "cvv.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "cmap.mm"
include "df-map.mm"
include "reldmmpt2.mm"

theorem reldmmap
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- Rel dom ^m

  proof
    vx
    vy
    cvv
    cvv
    vy
    cv
    vx
    cv
    vf
    cv
    wf
    vf
    cab
    cmap
    vx
    vy
    vf
    df-map
    reldmmpt2
end
