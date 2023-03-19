include "weq.mm"
include "wal.mm"
include "wi.mm"
include "equid.mm"
include "pm2.24i.mm"

theorem ax13dgen1
  let vx: setvar x
  let vz: setvar z


  assert |- ( -. x = x -> ( x = z -> A. x x = z ) )

  proof
    vx
    vx
    weq
    vx
    vz
    weq
    #
    @0
    vx
    wal
    wi
    vx
    equid
    pm2.24i
end
