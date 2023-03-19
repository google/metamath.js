include "wa.mm"
include "wex.mm"
include "19.40.mm"
include "19.9v.mm"
include "anbi2i.mm"
include "sylib.mm"
include "pm3.21.mm"
include "eximdv.mm"
include "impcom.mm"
include "impbii.mm"

theorem 19.41v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    wex
    #
    wph
    vx
    wex
    #
    wps
    wa
    #
    @1
    @2
    wps
    vx
    wex
    #
    wa
    @3
    wph
    wps
    vx
    19.40
    @4
    wps
    @2
    wps
    vx
    19.9v
    anbi2i
    sylib
    wps
    @2
    @1
    wps
    wph
    @0
    vx
    wps
    wph
    pm3.21
    eximdv
    impcom
    impbii
end
