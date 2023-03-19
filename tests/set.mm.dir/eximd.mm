include "nf5ri.mm"
include "eximdh.mm"

theorem eximd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
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
