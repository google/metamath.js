include "cr.mm"
include "clt.mm"
include "cv.mm"
include "axlttri.mm"
include "lttr.mm"
include "isso2i.mm"

theorem ltso
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- < Or RR

  proof
    vx
    vy
    vz
    cr
    clt
    vx
    cv
    #
    vy
    cv
    #
    axlttri
    @0
    @1
    vz
    cv
    lttr
    isso2i
end
