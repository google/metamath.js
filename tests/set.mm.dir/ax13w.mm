include "weq.mm"
include "wn.mm"
include "ax5d.mm"

theorem ax13w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( -. x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    weq
    wn
    vy
    vz
    weq
    vx
    ax5d
end
