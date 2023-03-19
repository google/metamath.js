include "imp.mm"
include "exlimddv.mm"

theorem exlimimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimimd.1: |- ( ph -> E. x ps )
  assume exlimimd.2: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    vx
    exlimimd.1
    wph
    wps
    wch
    exlimimd.2
    imp
    exlimddv
end
