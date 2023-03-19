include "weq.mm"
include "a1i.mm"
include "cdeqi.mm"

theorem cdeqth
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume cdeqth.1: |- ph


  assert |- CondEq ( x = y -> ph )

  proof
    wph
    vx
    vy
    wph
    vx
    vy
    weq
    cdeqth.1
    a1i
    cdeqi
end
