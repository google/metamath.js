include "wal.mm"
include "wi.mm"
include "nfim1.mm"
include "weq.mm"
include "com12.mm"
include "a2d.mm"
include "cbv3.mm"
include "19.21.mm"
include "3imtr3i.mm"
include "pm2.86i.mm"

theorem cbv1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbv1.1: |- F/ x ph
  assume cbv1.2: |- F/ y ph
  assume cbv1.3: |- ( ph -> F/ y ps )
  assume cbv1.4: |- ( ph -> F/ x ch )
  assume cbv1.5: |- ( ph -> ( x = y -> ( ps -> ch ) ) )


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
    cbv1.2
    cbv1.3
    nfim1
    wph
    wch
    vx
    cbv1.1
    cbv1.4
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
    cbv1.5
    com12
    a2d
    cbv3
    wph
    wps
    vx
    cbv1.1
    19.21
    wph
    wch
    vy
    cbv1.2
    19.21
    3imtr3i
    pm2.86i
end
