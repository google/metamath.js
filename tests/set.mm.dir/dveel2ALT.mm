include "wel.mm"
include "ax5el.mm"
include "elequ2.mm"
include "dvelimh.mm"

theorem dveel2ALT
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
    vz
    vw
    vx
    ax5el
    vz
    vy
    vw
    ax5el
    vw
    vy
    vz
    elequ2
    dvelimh
end
