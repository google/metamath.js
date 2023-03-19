include "wcdeq.mm"
include "weq.mm"
include "wi.mm"
include "df-cdeq.mm"
include "mpbir.mm"

theorem cdeqi
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume cdeqi.1: |- ( x = y -> ph )


  assert |- CondEq ( x = y -> ph )

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
    cdeqi.1
    wph
    vx
    vy
    df-cdeq
    mpbir
end
