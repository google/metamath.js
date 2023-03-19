include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wnf.mm"
include "wb.mm"
include "19.23t.mm"
include "syl.mm"
include "pm5.74d.mm"
include "albid.mm"
include "ax6e.mm"
include "a1bi.mm"
include "a1i.mm"
include "3bitr4d.mm"

theorem wl-equsald
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume wl-equsald.1: |- F/ x ph
  assume wl-equsald.2: |- ( ph -> F/ x ch )
  assume wl-equsald.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( A. x ( x = y -> ps ) <-> ch ) )

  proof
    wph
    vx
    vy
    weq
    #
    wch
    wi
    #
    vx
    wal
    #
    @0
    vx
    wex
    #
    wch
    wi
    #
    @0
    wps
    wi
    #
    vx
    wal
    wch
    wph
    wch
    vx
    wnf
    @2
    @4
    wb
    wl-equsald.2
    @0
    wch
    vx
    19.23t
    syl
    wph
    @5
    @1
    vx
    wl-equsald.1
    wph
    @0
    wps
    wch
    wl-equsald.3
    pm5.74d
    albid
    wch
    @4
    wb
    wph
    @3
    wch
    vx
    vy
    ax6e
    a1bi
    a1i
    3bitr4d
end
