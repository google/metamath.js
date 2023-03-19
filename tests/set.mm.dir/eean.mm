include "wa.mm"
include "wex.mm"
include "19.42.mm"
include "exbii.mm"
include "nfex.mm"
include "19.41.mm"
include "bitri.mm"

theorem eean
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume eean.1: |- F/ y ph
  assume eean.2: |- F/ x ps


  assert |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) )

  proof
    wph
    wps
    wa
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
    wa
    #
    vx
    wex
    wph
    vx
    wex
    @1
    wa
    @0
    @2
    vx
    wph
    wps
    vy
    eean.1
    19.42
    exbii
    wph
    @1
    vx
    wps
    vx
    vy
    eean.2
    nfex
    19.41
    bitri
end
