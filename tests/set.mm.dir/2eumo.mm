include "weu.mm"
include "wmo.mm"
include "wi.mm"
include "euimmo.mm"
include "eumo.mm"
include "mpg.mm"

theorem 2eumo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x E* y ph -> E* x E! y ph )

  proof
    wph
    vy
    weu
    #
    wph
    vy
    wmo
    #
    wi
    @1
    vx
    weu
    @0
    vx
    wmo
    wi
    vx
    @0
    @1
    vx
    euimmo
    wph
    vy
    eumo
    mpg
end
