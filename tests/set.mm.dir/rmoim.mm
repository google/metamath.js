include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wal.mm"
include "wrmo.mm"
include "df-ral.mm"
include "imdistan.mm"
include "albii.mm"
include "bitri.mm"
include "wmo.mm"
include "moim.mm"
include "df-rmo.mm"
include "3imtr4g.mm"
include "sylbi.mm"

theorem rmoim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph -> ps ) -> ( E* x e. A ps -> E* x e. A ph ) )

  proof
    wph
    wps
    wi
    #
    vx
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    @2
    wps
    wa
    #
    wi
    #
    vx
    wal
    #
    wps
    vx
    cA
    wrmo
    #
    wph
    vx
    cA
    wrmo
    #
    wi
    @1
    @2
    @0
    wi
    #
    vx
    wal
    @6
    @0
    vx
    cA
    df-ral
    @9
    @5
    vx
    @2
    wph
    wps
    imdistan
    albii
    bitri
    @6
    @4
    vx
    wmo
    @3
    vx
    wmo
    @7
    @8
    @3
    @4
    vx
    moim
    wps
    vx
    cA
    df-rmo
    wph
    vx
    cA
    df-rmo
    3imtr4g
    sylbi
end
