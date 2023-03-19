include "weq.mm"
include "wex.mm"
include "wi.mm"
include "wn.mm"
include "wal.mm"
include "eximi.mm"
include "df-ex.mm"
include "19.35.mm"
include "3imtr3i.mm"

theorem speimfwALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume speimfw.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) )

  proof
    vx
    vy
    weq
    #
    vx
    wex
    wph
    wps
    wi
    #
    vx
    wex
    @0
    wn
    vx
    wal
    wn
    wph
    vx
    wal
    wps
    vx
    wex
    wi
    @0
    @1
    vx
    speimfw.2
    eximi
    @0
    vx
    df-ex
    wph
    wps
    vx
    19.35
    3imtr3i
end
