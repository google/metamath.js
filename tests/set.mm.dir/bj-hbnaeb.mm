include "weq.mm"
include "wal.mm"
include "wn.mm"
include "hbnae.mm"
include "sp.mm"
include "impbii.mm"

theorem bj-hbnaeb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = y <-> A. z -. A. x x = y )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    @0
    vz
    wal
    vx
    vy
    vz
    hbnae
    @0
    vz
    sp
    impbii
end
