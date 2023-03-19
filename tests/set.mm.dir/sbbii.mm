include "wsb.mm"
include "biimpi.mm"
include "sbimi.mm"
include "biimpri.mm"
include "impbii.mm"

theorem sbbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
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
