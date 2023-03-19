include "weq.mm"
include "wal.mm"
include "hbae-o.mm"
include "hbn.mm"

theorem hbnae-o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = y -> A. z -. A. x x = y )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vx
    vy
    vz
    hbae-o
    hbn
end
