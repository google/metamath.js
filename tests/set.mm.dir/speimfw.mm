include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "df-ex.mm"
include "biimpri.mm"
include "com12.mm"
include "aleximi.mm"
include "syl5com.mm"

theorem speimfw
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume speimfw.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) )

  proof
    vx
    vy
    weq
    #
    wn
    vx
    wal
    wn
    #
    @0
    vx
    wex
    #
    wph
    vx
    wal
    wps
    vx
    wex
    @2
    @1
    @0
    vx
    df-ex
    biimpri
    wph
    @0
    wps
    vx
    @0
    wph
    wps
    speimfw.2
    com12
    aleximi
    syl5com
end
