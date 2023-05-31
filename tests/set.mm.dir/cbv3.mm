include "wal.mm"
include "nfal.mm"
include "spim.mm"
include "alrimi.mm"

theorem cbv3
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume cbv3.1: |- F/ y ph
  assume cbv3.2: |- F/ x ps
  assume cbv3.3: |- ( x = y -> ( ph -> ps ) )


  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    wph
    vy
    vx
    cbv3.1
    nfal
    wph
    wps
    vx
    vy
    cbv3.2
    cbv3.3
    spim
    alrimi
end
