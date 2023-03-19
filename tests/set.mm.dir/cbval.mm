include "wal.mm"
include "weq.mm"
include "biimpd.mm"
include "cbv3.mm"
include "wi.mm"
include "biimprd.mm"
include "equcoms.mm"
include "impbii.mm"

theorem cbval
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbval.1: |- F/ y ph
  assume cbval.2: |- F/ x ps
  assume cbval.3: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x ph <-> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    wal
    wph
    wps
    vx
    vy
    cbval.1
    cbval.2
    vx
    vy
    weq
    #
    wph
    wps
    cbval.3
    biimpd
    cbv3
    wps
    wph
    vy
    vx
    cbval.2
    cbval.1
    wps
    wph
    wi
    vx
    vy
    @0
    wph
    wps
    cbval.3
    biimprd
    equcoms
    cbv3
    impbii
end
