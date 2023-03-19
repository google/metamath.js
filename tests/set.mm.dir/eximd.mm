include "nf5ri.mm"
include "eximdh.mm"

theorem eximd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume eximd.1: |- F/ x ph
  assume eximd.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( E. x ps -> E. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    eximd.1
    nf5ri
    eximd.2
    eximdh
end
