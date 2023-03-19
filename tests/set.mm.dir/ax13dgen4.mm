include "weq.mm"
include "wal.mm"
include "pm2.21.mm"

theorem ax13dgen4
  let vx: setvar x


  assert |- ( -. x = x -> ( x = x -> A. x x = x ) )

  proof
    vx
    vx
    weq
    #
    @0
    vx
    wal
    pm2.21
end
