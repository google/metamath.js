include "weq.mm"
include "wn.mm"
include "wal.mm"
include "equidqe.mm"
include "pm2.21i.mm"

theorem axc5sp1
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. y -. x = x -> -. x = x )

  proof
    vx
    vx
    weq
    wn
    #
    vy
    wal
    @0
    vx
    vy
    equidqe
    pm2.21i
end
