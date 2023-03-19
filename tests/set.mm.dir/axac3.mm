include "wac.mm"
include "wel.mm"
include "weq.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "wal.mm"
include "wex.mm"
include "ax-ac2.mm"
include "ax-gen.mm"
include "dfackm.mm"
include "mpbir.mm"

theorem axac3
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- CHOICE

  proof
    wac
    vy
    vx
    wel
    #
    vz
    vy
    wel
    vw
    vx
    wel
    vy
    vw
    weq
    wn
    wa
    vz
    vw
    wel
    wa
    wi
    wa
    @0
    wn
    vz
    vx
    wel
    vw
    vz
    wel
    vw
    vy
    wel
    wa
    vv
    vz
    wel
    vv
    vy
    wel
    wa
    vv
    vw
    weq
    wi
    wa
    wi
    wa
    wo
    vv
    wal
    vw
    wex
    vz
    wal
    vy
    wex
    #
    vx
    wal
    @1
    vx
    vx
    vy
    vz
    vw
    vv
    ax-ac2
    ax-gen
    vx
    vy
    vz
    vw
    vv
    dfackm
    mpbir
end
