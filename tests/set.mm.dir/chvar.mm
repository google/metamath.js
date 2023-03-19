include "weq.mm"
include "biimpd.mm"
include "spim.mm"
include "mpg.mm"

theorem chvar
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume chvar.1: |- F/ x ps
  assume chvar.2: |- ( x = y -> ( ph <-> ps ) )
  assume chvar.3: |- ph


  assert |- ps

  proof
    wph
    wps
    vx
    wph
    wps
    vx
    vy
    chvar.1
    vx
    vy
    weq
    wph
    wps
    chvar.2
    biimpd
    spim
    chvar.3
    mpg
end
