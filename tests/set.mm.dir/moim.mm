include "wi.mm"
include "wal.mm"
include "weq.mm"
include "wex.mm"
include "wmo.mm"
include "imim1.mm"
include "al2imi.mm"
include "eximdv.mm"
include "mo2v.mm"
include "3imtr4g.mm"

theorem moim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    #
    wps
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wph
    @2
    wi
    #
    vx
    wal
    #
    vy
    wex
    wps
    vx
    wmo
    wph
    vx
    wmo
    @1
    @4
    @6
    vy
    @0
    @3
    @5
    vx
    wph
    wps
    @2
    imim1
    al2imi
    eximdv
    wps
    vx
    vy
    mo2v
    wph
    vx
    vy
    mo2v
    3imtr4g
end
