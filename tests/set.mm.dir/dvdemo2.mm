include "wel.mm"
include "weq.mm"
include "wi.mm"
include "el.mm"
include "ax-1.mm"
include "eximii.mm"

theorem dvdemo2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- E. x ( x = y -> z e. x )

  proof
    vz
    vx
    wel
    #
    vx
    vy
    weq
    #
    @0
    wi
    vx
    vz
    vx
    el
    @0
    @1
    ax-1
    eximii
end
