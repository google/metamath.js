include "wex.mm"
include "nfe1.mm"
include "19.23.mm"

theorem bj-biexex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> E. x ps ) <-> ( E. x ph -> E. x ps ) )

  proof
    wph
    wps
    vx
    wex
    vx
    wps
    vx
    nfe1
    19.23
end
