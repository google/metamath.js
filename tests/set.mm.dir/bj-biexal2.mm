include "wex.mm"
include "nfe1.mm"
include "19.21.mm"

theorem bj-biexal2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( E. x ph -> ps ) <-> ( E. x ph -> A. x ps ) )

  proof
    wph
    vx
    wex
    wps
    vx
    wph
    vx
    nfe1
    19.21
end
