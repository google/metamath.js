include "nfv.mm"
include "chvar.mm"

theorem chvarvOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume chvarv.1: |- ( x = y -> ( ph <-> ps ) )
  assume chvarv.2: |- ph

  disjoint ps x
  assert |- ps

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    chvarv.1
    chvarv.2
    chvar
end
