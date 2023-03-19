include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bj-alequex.mm"
include "19.35.mm"
include "sylib.mm"
include "imim1d.mm"

theorem bj-spimt2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( x = y -> ( ph -> ps ) ) -> ( ( E. x ps -> ps ) -> ( A. x ph -> ps ) ) )

  proof
    vx
    vy
    weq
    wph
    wps
    wi
    #
    wi
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wps
    @1
    @0
    vx
    wex
    @2
    @3
    wi
    @0
    vx
    vy
    bj-alequex
    wph
    wps
    vx
    19.35
    sylib
    imim1d
end
