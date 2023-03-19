include "wmo.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "nfmo1.mm"
include "nfe1.mm"
include "nfan.mm"
include "mopick.mm"
include "ancld.mm"
include "anim1d.mm"
include "df-3an.mm"
include "syl6ibr.mm"
include "eximd.mm"
include "3impia.mm"

theorem mopick2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) -> E. x ( ph /\ ps /\ ch ) )

  proof
    wph
    vx
    wmo
    #
    wph
    wps
    wa
    #
    vx
    wex
    #
    wph
    wch
    wa
    #
    vx
    wex
    wph
    wps
    wch
    w3a
    #
    vx
    wex
    @0
    @2
    wa
    #
    @3
    @4
    vx
    @0
    @2
    vx
    wph
    vx
    nfmo1
    @1
    vx
    nfe1
    nfan
    @5
    @3
    @1
    wch
    wa
    @4
    @5
    wph
    @1
    wch
    @5
    wph
    wps
    wph
    wps
    vx
    mopick
    ancld
    anim1d
    wph
    wps
    wch
    df-3an
    syl6ibr
    eximd
    3impia
end
