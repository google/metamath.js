include "wal.mm"
include "wb.mm"
include "weq.mm"
include "cdeqri.mm"
include "albidv.mm"
include "cdeqi.mm"

theorem cdeqal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cdeqnot.1: |- CondEq ( x = y -> ( ph <-> ps ) )

  disjoint x z
  disjoint y z
  assert |- CondEq ( x = y -> ( A. z ph <-> A. z ps ) )

  proof
    wph
    vz
    wal
    wps
    vz
    wal
    wb
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
    albidv
    cdeqi
end
