include "wo.mm"
include "wex.mm"
include "19.43.mm"
include "19.9.mm"
include "orbi2i.mm"
include "bitri.mm"

theorem 19.44
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.44.1: |- F/ x ps


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
    19.44.1
    19.9
    orbi2i
    bitri
end
