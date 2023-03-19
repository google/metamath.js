include "weq.mm"
include "wal.mm"
include "wn.mm"
include "equid.mm"
include "ax-gen.mm"
include "2a1i.mm"

theorem ax13dgen3
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. x = y -> ( y = y -> A. x y = y ) )

  proof
    vy
    vy
    weq
    #
    vx
    wal
    vx
    vy
    weq
    wn
    @0
    @0
    vx
    vy
    equid
    ax-gen
    2a1i
end
