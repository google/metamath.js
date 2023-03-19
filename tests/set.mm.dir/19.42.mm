include "wa.mm"
include "wex.mm"
include "19.41.mm"
include "exancom.mm"
include "ancom.mm"
include "3bitr4i.mm"

theorem 19.42
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.42.1: |- F/ x ph


  assert |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) )

  proof
    wps
    wph
    wa
    vx
    wex
    wps
    vx
    wex
    #
    wph
    wa
    wph
    wps
    wa
    vx
    wex
    wph
    @0
    wa
    wps
    wph
    vx
    19.42.1
    19.41
    wph
    wps
    vx
    exancom
    wph
    @0
    ancom
    3bitr4i
end
