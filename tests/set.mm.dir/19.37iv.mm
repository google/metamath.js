include "wi.mm"
include "wex.mm"
include "19.37v.mm"
include "mpbi.mm"

theorem 19.37iv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.37iv.1: |- E. x ( ph -> ps )

  disjoint ph x
  assert |- ( ph -> E. x ps )

  proof
    wph
    wps
    wi
    vx
    wex
    wph
    wps
    vx
    wex
    wi
    19.37iv.1
    wph
    wps
    vx
    19.37v
    mpbi
end
