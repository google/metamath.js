include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.23.mm"
include "pm5.74i.mm"
include "albii.mm"
include "ax6e.mm"
include "a1bi.mm"
include "3bitr4i.mm"

theorem equsal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsal.1: |- F/ x ps
  assume equsal.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x ( x = y -> ph ) <-> ps )

  proof
    vx
    vy
    weq
    #
    wps
    wi
    #
    vx
    wal
    @0
    vx
    wex
    #
    wps
    wi
    @0
    wph
    wi
    #
    vx
    wal
    wps
    @0
    wps
    vx
    equsal.1
    19.23
    @3
    @1
    vx
    @0
    wph
    wps
    equsal.2
    pm5.74i
    albii
    @2
    wps
    vx
    vy
    ax6e
    a1bi
    3bitr4i
end
