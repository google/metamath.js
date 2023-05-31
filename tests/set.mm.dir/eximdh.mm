include "wal.mm"
include "wex.mm"
include "wi.mm"
include "aleximi.mm"
include "syl.mm"

theorem eximdh
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume eximdh.1: |- ( ph -> A. x ph )
  assume eximdh.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( E. x ps -> E. x ch ) )

  proof
    wph
    wph
    vx
    wal
    wps
    vx
    wex
    wch
    vx
    wex
    wi
    eximdh.1
    wph
    wps
    wch
    vx
    eximdh.2
    aleximi
    syl
end
