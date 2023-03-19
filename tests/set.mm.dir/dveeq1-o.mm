include "weq.mm"
include "ax-5.mm"
include "equequ1.mm"
include "dvelimf-o.mm"

theorem dveeq1-o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w z
  disjoint w x
  disjoint w y
  assert |- ( -. A. x x = y -> ( y = z -> A. x y = z ) )

  proof
    vw
    vz
    weq
    #
    vy
    vz
    weq
    #
    vx
    vy
    vw
    @0
    vx
    ax-5
    @1
    vw
    ax-5
    vw
    vy
    vz
    equequ1
    dvelimf-o
end
