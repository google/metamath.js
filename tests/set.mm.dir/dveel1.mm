include "wel.mm"
include "elequ1.mm"
include "dvelimv.mm"

theorem dveel1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w z
  disjoint w x
  disjoint w y
  assert |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) )

  proof
    vw
    vz
    wel
    vy
    vz
    wel
    vx
    vy
    vw
    vw
    vy
    vz
    elequ1
    dvelimv
end
