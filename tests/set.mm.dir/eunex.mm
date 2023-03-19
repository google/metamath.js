include "wex.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wn.mm"
include "weu.mm"
include "dtru.mm"
include "alim.mm"
include "mtoi.mm"
include "exlimiv.mm"
include "adantl.mm"
include "eu3v.mm"
include "exnal.mm"
include "3imtr4i.mm"

theorem eunex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x ph -> E. x -. ph )

  proof
    wph
    vx
    wex
    #
    wph
    vx
    vy
    weq
    #
    wi
    vx
    wal
    #
    vy
    wex
    #
    wa
    wph
    vx
    wal
    #
    wn
    #
    wph
    vx
    weu
    wph
    wn
    vx
    wex
    @3
    @5
    @0
    @2
    @5
    vy
    @2
    @4
    @1
    vx
    wal
    vx
    vy
    dtru
    wph
    @1
    vx
    alim
    mtoi
    exlimiv
    adantl
    wph
    vx
    vy
    eu3v
    wph
    vx
    exnal
    3imtr4i
end
