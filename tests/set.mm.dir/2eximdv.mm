include "wex.mm"
include "eximdv.mm"

theorem 2eximdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume 2alimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) )

  proof
    wph
    wps
    vy
    wex
    wch
    vy
    wex
    vx
    wph
    wps
    wch
    vy
    2alimdv.1
    eximdv
    eximdv
end
