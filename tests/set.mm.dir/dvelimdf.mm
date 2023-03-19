include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wnf.mm"
include "nfim1.mm"
include "wb.mm"
include "com12.mm"
include "pm5.74d.mm"
include "dvelimf.mm"
include "pm5.5.mm"
include "nfbidf.mm"
include "syl5ib.mm"

theorem dvelimdf
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assume dvelimdf.1: |- F/ x ph
  assume dvelimdf.2: |- F/ z ph
  assume dvelimdf.3: |- ( ph -> F/ x ps )
  assume dvelimdf.4: |- ( ph -> F/ z ch )
  assume dvelimdf.5: |- ( ph -> ( z = y -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( -. A. x x = y -> F/ x ch ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    wph
    wch
    wi
    #
    vx
    wnf
    wph
    wch
    vx
    wnf
    wph
    wps
    wi
    @0
    vx
    vy
    vz
    wph
    wps
    vx
    dvelimdf.1
    dvelimdf.3
    nfim1
    wph
    wch
    vz
    dvelimdf.2
    dvelimdf.4
    nfim1
    vz
    vy
    weq
    #
    wph
    wps
    wch
    wph
    @1
    wps
    wch
    wb
    dvelimdf.5
    com12
    pm5.74d
    dvelimf
    wph
    @0
    wch
    vx
    dvelimdf.1
    wph
    wch
    pm5.5
    nfbidf
    syl5ib
end
