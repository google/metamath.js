include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfnae.mm"
include "sbf.mm"

theorem sbequ6
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vz
    vw
    vx
    vy
    vz
    nfnae
    sbf
end
