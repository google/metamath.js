include "wcdeq.mm"
include "weq.mm"
include "wi.mm"
include "df-cdeq.mm"
include "mpbi.mm"

theorem cdeqri
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume cdeqri.1: |- CondEq ( x = y -> ph )


  assert |- ( x = y -> ph )

  proof
    wph
    vx
    vy
    wcdeq
    vx
    vy
    weq
    wph
    wi
    cdeqri.1
    wph
    vx
    vy
    df-cdeq
    mpbi
end
