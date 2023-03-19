include "weq.mm"
include "equequ1.mm"
include "hbn1w.mm"

theorem wl-naevhba1v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( -. A. x x = y -> A. x -. A. x x = y )

  proof
    vx
    vy
    weq
    vz
    vy
    weq
    vx
    vz
    vx
    vz
    vy
    equequ1
    hbn1w
end
