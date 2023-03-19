include "ax-5.mm"
include "eximdh.mm"

theorem eximdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x ps -> E. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    ax-5
    alimdv.1
    eximdh
end
