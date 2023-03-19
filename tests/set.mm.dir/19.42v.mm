include "wa.mm"
include "wex.mm"
include "19.41v.mm"
include "exancom.mm"
include "ancom.mm"
include "3bitr4i.mm"

theorem 19.42v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
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
    19.41v
    wph
    wps
    vx
    exancom
    wph
    @0
    ancom
    3bitr4i
end
