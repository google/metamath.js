include "weu.mm"
include "wex.mm"
include "euex.mm"
include "eximi.mm"
include "syl.mm"

theorem 2eu2ex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x E! y ph -> E. x E. y ph )

  proof
    wph
    vy
    weu
    #
    vx
    weu
    @0
    vx
    wex
    wph
    vy
    wex
    #
    vx
    wex
    @0
    vx
    euex
    @0
    @1
    vx
    wph
    vy
    euex
    eximi
    syl
end
