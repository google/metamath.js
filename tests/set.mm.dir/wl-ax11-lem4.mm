include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "ancom.mm"
include "nfna1.mm"
include "wl-ax11-lem3.mm"
include "nfan1.mm"
include "nfxfr.mm"

theorem wl-ax11-lem4
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint u x
  assert |- F/ x ( A. u u = y /\ -. A. x x = y )

  proof
    vu
    vy
    weq
    vu
    wal
    #
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    wa
    @2
    @0
    wa
    vx
    @0
    @2
    ancom
    @2
    @0
    vx
    @1
    vx
    nfna1
    vx
    vy
    vu
    wl-ax11-lem3
    nfan1
    nfxfr
end
