include "wex.mm"
include "exlimdv.mm"

theorem exlimdvv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume exlimdvv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ch x
  disjoint ph x
  disjoint ch y
  disjoint ph y
  assert |- ( ph -> ( E. x E. y ps -> ch ) )

  proof
    wph
    wps
    vy
    wex
    wch
    vx
    wph
    wps
    wch
    vy
    exlimdvv.1
    exlimdv
    exlimdv
end
