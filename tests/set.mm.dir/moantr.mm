include "wmo.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "w3a.mm"
include "exancom.mm"
include "anbi1i.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "mopick2.mm"
include "sylbi.mm"
include "exbii.mm"
include "exsimpr.mm"
include "syl.mm"
include "impexp.mm"
include "mpbi.mm"

theorem moantr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( E* x ps -> ( ( E. x ( ph /\ ps ) /\ E. x ( ps /\ ch ) ) -> E. x ( ph /\ ch ) ) )

  proof
    wps
    vx
    wmo
    #
    wph
    wps
    wa
    vx
    wex
    #
    wps
    wch
    wa
    vx
    wex
    #
    wa
    #
    wa
    #
    wph
    wch
    wa
    #
    vx
    wex
    #
    wi
    @0
    @3
    @6
    wi
    wi
    @4
    wps
    wph
    wch
    w3a
    #
    vx
    wex
    #
    @6
    @4
    @0
    wps
    wph
    wa
    vx
    wex
    #
    @2
    w3a
    #
    @8
    @4
    @0
    @9
    @2
    wa
    #
    wa
    @10
    @3
    @11
    @0
    @1
    @9
    @2
    wph
    wps
    vx
    exancom
    anbi1i
    anbi2i
    @0
    @9
    @2
    3anass
    bitr4i
    wps
    wph
    wch
    vx
    mopick2
    sylbi
    @8
    wps
    @5
    wa
    #
    vx
    wex
    @6
    @7
    @12
    vx
    wps
    wph
    wch
    3anass
    exbii
    wps
    @5
    vx
    exsimpr
    sylbi
    syl
    @0
    @3
    @6
    impexp
    mpbi
end
