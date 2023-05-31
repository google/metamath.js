include "wsb.mm"
include "biimpi.mm"
include "sbimi.mm"
include "biimpri.mm"
include "impbii.mm"

theorem sbbii
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume sbbii.1: |- ( ph <-> ps )


  assert |- ( [ y / x ] ph <-> [ y / x ] ps )

  proof
    wph
    vx
    vy
    wsb
    wps
    vx
    vy
    wsb
    wph
    wps
    vx
    vy
    wph
    wps
    sbbii.1
    biimpi
    sbimi
    wps
    wph
    vx
    vy
    wph
    wps
    sbbii.1
    biimpri
    sbimi
    impbii
end
