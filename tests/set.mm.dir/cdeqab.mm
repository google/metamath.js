include "cab.mm"
include "wceq.mm"
include "weq.mm"
include "wb.mm"
include "cdeqri.mm"
include "abbidv.mm"
include "cdeqi.mm"

theorem cdeqab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cdeqnot.1: |- CondEq ( x = y -> ( ph <-> ps ) )

  disjoint x z
  disjoint y z
  assert |- CondEq ( x = y -> { z | ph } = { z | ps } )

  proof
    wph
    vz
    cab
    wps
    vz
    cab
    wceq
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    vz
    wph
    wps
    wb
    vx
    vy
    cdeqnot.1
    cdeqri
    abbidv
    cdeqi
end
