include "weq.mm"
include "equequ2.mm"
include "dvelimv.mm"

theorem dveeq2ALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w x
  disjoint w z
  disjoint w y
  assert |- ( -. A. x x = y -> ( z = y -> A. x z = y ) )

  proof
    vz
    vw
    weq
    vz
    vy
    weq
    vx
    vy
    vw
    vw
    vy
    vz
    equequ2
    dvelimv
end
