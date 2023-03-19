include "wmo.mm"
include "wa.mm"
include "wi.mm"
include "id.mm"
include "nfmo1.mm"
include "moanim.mm"
include "mpbir.mm"
include "ancom.mm"
include "mobii.mm"

theorem moanmo
  let wph: wff ph
  let vx: setvar x


  assert |- E* x ( ph /\ E* x ph )

  proof
    wph
    wph
    vx
    wmo
    #
    wa
    #
    vx
    wmo
    @0
    wph
    wa
    #
    vx
    wmo
    #
    @3
    @0
    @0
    wi
    @0
    id
    @0
    wph
    vx
    wph
    vx
    nfmo1
    moanim
    mpbir
    @1
    @2
    vx
    wph
    @0
    ancom
    mobii
    mpbir
end
