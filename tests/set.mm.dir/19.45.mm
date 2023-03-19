include "wo.mm"
include "wex.mm"
include "19.43.mm"
include "19.9.mm"
include "orbi1i.mm"
include "bitri.mm"

theorem 19.45
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.45.1: |- F/ x ph


  assert |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) )

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
    wph
    @1
    wo
    wph
    wps
    vx
    19.43
    @0
    wph
    @1
    wph
    vx
    19.45.1
    19.9
    orbi1i
    bitri
end
