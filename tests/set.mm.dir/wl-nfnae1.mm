include "weq.mm"
include "wal.mm"
include "wl-nfae1.mm"
include "nfn.mm"

theorem wl-nfnae1
  let vx: setvar x
  let vy: setvar y


  assert |- F/ x -. A. y y = x

  proof
    vy
    vx
    weq
    vy
    wal
    vx
    vx
    vy
    wl-nfae1
    nfn
end
