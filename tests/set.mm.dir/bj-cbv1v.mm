include "wal.mm"
include "wi.mm"
include "nfim1.mm"
include "weq.mm"
include "com12.mm"
include "a2d.mm"
include "cbv3v.mm"
include "19.21.mm"
include "3imtr3i.mm"
include "pm2.86i.mm"

theorem bj-cbv1v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbv1v.1: |- F/ x ph
  assume bj-cbv1v.2: |- F/ y ph
  assume bj-cbv1v.3: |- ( ph -> F/ y ps )
  assume bj-cbv1v.4: |- ( ph -> F/ x ch )
  assume bj-cbv1v.5: |- ( ph -> ( x = y -> ( ps -> ch ) ) )

  disjoint x y
  assert |- ( ph -> ( A. x ps -> A. y ch ) )

  proof
    wph
    wps
    vx
    wal
    #
    wch
    vy
    wal
    #
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
    @0
    wi
    wph
    @1
    wi
    @2
    @3
    vx
    vy
    wph
    wps
    vy
    bj-cbv1v.2
    bj-cbv1v.3
    nfim1
    wph
    wch
    vx
    bj-cbv1v.1
    bj-cbv1v.4
    nfim1
    vx
    vy
    weq
    #
    wph
    wps
    wch
    wph
    @4
    wps
    wch
    wi
    bj-cbv1v.5
    com12
    a2d
    cbv3v
    wph
    wps
    vx
    bj-cbv1v.1
    19.21
    wph
    wch
    vy
    bj-cbv1v.2
    19.21
    3imtr3i
    pm2.86i
end
