include "weq.mm"
include "wal.mm"
include "aecom.mm"
include "nfa1.mm"
include "nfxfr.mm"

theorem wl-nfae1
  let vx: setvar x
  let vy: setvar y


  assert |- F/ x A. y y = x

  proof
    vy
    vx
    weq
    vy
    wal
    vx
    vy
    weq
    #
    vx
    wal
    vx
    vy
    vx
    aecom
    @0
    vx
    nfa1
    nfxfr
end
