include "weu.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "wi.mm"
include "eupick.mm"
include "3adant2.mm"
include "exancom.mm"
include "sylan2b.mm"
include "3adant1.mm"
include "impbid.mm"

theorem eupickb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) -> ( ph <-> ps ) )

  proof
    wph
    vx
    weu
    #
    wps
    vx
    weu
    #
    wph
    wps
    wa
    vx
    wex
    #
    w3a
    wph
    wps
    @0
    @2
    wph
    wps
    wi
    @1
    wph
    wps
    vx
    eupick
    3adant2
    @1
    @2
    wps
    wph
    wi
    #
    @0
    @2
    @1
    wps
    wph
    wa
    vx
    wex
    @3
    wph
    wps
    vx
    exancom
    wps
    wph
    vx
    eupick
    sylan2b
    3adant1
    impbid
end
