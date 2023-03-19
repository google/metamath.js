include "wo.mm"
include "wex.mm"
include "19.45.mm"
include "exbii.mm"
include "nfex.mm"
include "19.44.mm"
include "bitri.mm"

theorem eeor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume eeor.1: |- F/ y ph
  assume eeor.2: |- F/ x ps


  assert |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) )

  proof
    wph
    wps
    wo
    vy
    wex
    #
    vx
    wex
    wph
    wps
    vy
    wex
    #
    wo
    #
    vx
    wex
    wph
    vx
    wex
    @1
    wo
    @0
    @2
    vx
    wph
    wps
    vy
    eeor.1
    19.45
    exbii
    wph
    @1
    vx
    wps
    vx
    vy
    eeor.2
    nfex
    19.44
    bitri
end
