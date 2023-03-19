include "wal.mm"
include "wb.mm"
include "cdeqri.mm"
include "cbvalv.mm"
include "cdeqth.mm"

theorem cdeqal1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cdeqnot.1: |- CondEq ( x = y -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  assert |- CondEq ( x = y -> ( A. x ph <-> A. y ps ) )

  proof
    wph
    vx
    wal
    wps
    vy
    wal
    wb
    vx
    vy
    wph
    wps
    vx
    vy
    wph
    wps
    wb
    vx
    vy
    cdeqnot.1
    cdeqri
    cbvalv
    cdeqth
end
