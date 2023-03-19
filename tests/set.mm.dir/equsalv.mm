include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.23.mm"
include "pm5.74i.mm"
include "albii.mm"
include "ax6ev.mm"
include "a1bi.mm"
include "3bitr4i.mm"

theorem equsalv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsalv.nf: |- F/ x ps
  assume equsalv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
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
    equsalv.nf
    19.23
    @3
    @1
    vx
    @0
    wph
    wps
    equsalv.1
    pm5.74i
    albii
    @2
    wps
    vx
    vy
    ax6ev
    a1bi
    3bitr4i
end
