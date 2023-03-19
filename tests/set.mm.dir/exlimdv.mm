include "wex.mm"
include "eximdv.mm"
include "ax5e.mm"
include "syl6.mm"

theorem exlimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ch x
  disjoint ph x
  assert |- ( ph -> ( E. x ps -> ch ) )

  proof
    wph
    wps
    vx
    wex
    wch
    vx
    wex
    wch
    wph
    wps
    wch
    vx
    exlimdv.1
    eximdv
    wch
    vx
    ax5e
    syl6
end
