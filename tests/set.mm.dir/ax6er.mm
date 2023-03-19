include "weq.mm"
include "ax6e.mm"
include "equcomi.mm"
include "eximii.mm"

theorem ax6er
  let vx: setvar x
  let vy: setvar y


  assert |- E. x y = x

  proof
    vx
    vy
    weq
    vy
    vx
    weq
    vx
    vx
    vy
    ax6e
    vx
    vy
    equcomi
    eximii
end
