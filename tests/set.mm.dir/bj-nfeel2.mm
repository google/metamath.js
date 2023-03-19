include "wel.mm"
include "nfv.mm"
include "elequ1.mm"
include "bj-dvelimv.mm"

theorem bj-nfeel2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t

  disjoint x z
  disjoint t x
  disjoint t z
  disjoint t y
  assert |- ( -. A. x x = y -> F/ x y e. z )

  proof
    vy
    vz
    wel
    vt
    vz
    wel
    #
    vx
    vy
    vt
    @0
    vx
    nfv
    vt
    vy
    vz
    elequ1
    bj-dvelimv
end
