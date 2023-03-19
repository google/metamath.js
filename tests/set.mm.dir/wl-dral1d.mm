include "weq.mm"
include "wal.mm"
include "wb.mm"
include "wi.mm"
include "com12.mm"
include "pm5.74d.mm"
include "sps.mm"
include "dral1.mm"
include "19.21.mm"
include "3bitr3g.mm"
include "pm5.74rd.mm"

theorem wl-dral1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume wl-dral1d.1: |- F/ x ph
  assume wl-dral1d.2: |- F/ y ph
  assume wl-dral1d.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( A. x x = y -> ( A. x ps <-> A. y ch ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wph
    wps
    vx
    wal
    #
    wch
    vy
    wal
    #
    wb
    @1
    wph
    @2
    @3
    @1
    wph
    wps
    wi
    #
    vx
    wal
    wph
    wch
    wi
    #
    vy
    wal
    wph
    @2
    wi
    wph
    @3
    wi
    @4
    @5
    vx
    vy
    @0
    @4
    @5
    wb
    vx
    @0
    wph
    wps
    wch
    wph
    @0
    wps
    wch
    wb
    wl-dral1d.3
    com12
    pm5.74d
    sps
    dral1
    wph
    wps
    vx
    wl-dral1d.1
    19.21
    wph
    wch
    vy
    wl-dral1d.2
    19.21
    3bitr3g
    pm5.74rd
    com12
end
