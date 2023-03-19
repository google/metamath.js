include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "wi.mm"
include "wal.mm"
include "moim.mm"
include "ax-mp.mm"
include "df-rmo.mm"
include "3imtr4i.mm"

theorem rmoimi2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rmoimi2.1: |- A. x ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) )


  assert |- ( E* x e. B ps -> E* x e. A ph )

  proof
    vx
    cv
    #
    cB
    wcel
    wps
    wa
    #
    vx
    wmo
    #
    @0
    cA
    wcel
    wph
    wa
    #
    vx
    wmo
    #
    wps
    vx
    cB
    wrmo
    wph
    vx
    cA
    wrmo
    @3
    @1
    wi
    vx
    wal
    @2
    @4
    wi
    rmoimi2.1
    @3
    @1
    vx
    moim
    ax-mp
    wps
    vx
    cB
    df-rmo
    wph
    vx
    cA
    df-rmo
    3imtr4i
end
