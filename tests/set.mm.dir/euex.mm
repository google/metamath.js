include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "df-eu.mm"
include "wi.mm"
include "ax6ev.mm"
include "biimpr.mm"
include "com12.mm"
include "eximii.mm"
include "19.35i.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem euex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x ph -> E. x ph )

  proof
    wph
    vx
    weu
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    wex
    #
    wph
    vx
    vy
    df-eu
    @2
    @3
    vy
    @1
    wph
    vx
    @0
    @1
    wph
    wi
    vx
    vx
    vy
    ax6ev
    @1
    @0
    wph
    wph
    @0
    biimpr
    com12
    eximii
    19.35i
    exlimiv
    sylbi
end
