include "weq.mm"
include "wi.mm"
include "ax6ev.mm"
include "equeucl.mm"
include "eximii.mm"
include "19.35i.mm"

theorem bj-ax6elem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( A. x y = z -> E. x x = y )

  proof
    vy
    vz
    weq
    #
    vx
    vy
    weq
    #
    vx
    vx
    vz
    weq
    @0
    @1
    wi
    vx
    vx
    vz
    ax6ev
    vx
    vy
    vz
    equeucl
    eximii
    19.35i
end
