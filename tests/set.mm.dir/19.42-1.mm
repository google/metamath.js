include "wex.mm"
include "wa.mm"
include "pm3.2.mm"
include "eximd.mm"
include "imp.mm"

theorem 19.42-1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.42.1: |- F/ x ph


  assert |- ( ( ph /\ E. x ps ) -> E. x ( ph /\ ps ) )

  proof
    wph
    wps
    vx
    wex
    wph
    wps
    wa
    #
    vx
    wex
    wph
    wps
    @0
    vx
    19.42.1
    wph
    wps
    pm3.2
    eximd
    imp
end
