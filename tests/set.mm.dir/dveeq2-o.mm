include "weq.mm"
include "ax-5.mm"
include "equequ2.mm"
include "dvelimf-o.mm"

theorem dveeq2-o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w z
  disjoint w x
  disjoint w y
  assert |- ( -. A. x x = y -> ( z = y -> A. x z = y ) )

  proof
    vz
    vw
    weq
    #
    vz
    vy
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
    equequ2
    dvelimf-o
end
