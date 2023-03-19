include "ch0o.mm"
include "cho.mm"
include "wcel.mm"
include "clo.mm"
include "0hmop.mm"
include "hmoplin.mm"
include "ax-mp.mm"

theorem 0lnop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- 0hop e. LinOp

  proof
    ch0o
    cho
    wcel
    ch0o
    clo
    wcel
    0hmop
    ch0o
    hmoplin
    ax-mp
end
