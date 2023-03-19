include "cvv.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "cmap.mm"
include "df-map.mm"
include "wcel.mm"
include "vex.mm"
include "mapex.mm"
include "mp2an.mm"
include "fnmpt2i.mm"

theorem fnmap
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ^m Fn ( _V X. _V )

  proof
    vx
    vy
    cvv
    cvv
    vy
    cv
    #
    vx
    cv
    #
    vf
    cv
    wf
    vf
    cab
    #
    cmap
    vx
    vy
    vf
    df-map
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    vy
    vex
    vx
    vex
    @0
    @1
    cvv
    cvv
    vf
    mapex
    mp2an
    fnmpt2i
end
