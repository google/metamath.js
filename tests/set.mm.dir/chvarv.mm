include "spv.mm"
include "mpg.mm"

theorem chvarv
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
    wph
    wps
    vx
    vy
    chvarv.1
    spv
    chvarv.2
    mpg
end
