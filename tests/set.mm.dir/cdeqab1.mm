include "cab.mm"
include "wceq.mm"
include "wb.mm"
include "cdeqri.mm"
include "cbvabv.mm"
include "cdeqth.mm"

theorem cdeqab1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cdeqnot.1: |- CondEq ( x = y -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  assert |- CondEq ( x = y -> { x | ph } = { y | ps } )

  proof
    wph
    vx
    cab
    wps
    vy
    cab
    wceq
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
    cbvabv
    cdeqth
end
