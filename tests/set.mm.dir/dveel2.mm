include "wel.mm"
include "elequ2.mm"
include "dvelimv.mm"

theorem dveel2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w z
  disjoint w x
  disjoint w y
  assert |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) )

  proof
    vz
    vw
    wel
    vz
    vy
    wel
    vx
    vy
    vw
    vw
    vy
    vz
    elequ2
    dvelimv
end
