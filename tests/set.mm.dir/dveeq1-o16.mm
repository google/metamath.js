include "weq.mm"
include "ax5eq.mm"
include "equequ1.mm"
include "dvelimh.mm"

theorem dveeq1-o16
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
    vy
    vz
    weq
    vx
    vy
    vw
    vw
    vz
    vx
    ax5eq
    vy
    vz
    vw
    ax5eq
    vw
    vy
    vz
    equequ1
    dvelimh
end
