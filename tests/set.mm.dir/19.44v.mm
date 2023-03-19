include "wo.mm"
include "wex.mm"
include "19.43.mm"
include "19.9v.mm"
include "orbi2i.mm"
include "bitri.mm"

theorem 19.44v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) )

  proof
    wph
    wps
    wo
    vx
    wex
    wph
    vx
    wex
    #
    wps
    vx
    wex
    #
    wo
    @0
    wps
    wo
    wph
    wps
    vx
    19.43
    @1
    wps
    @0
    wps
    vx
    19.9v
    orbi2i
    bitri
end
