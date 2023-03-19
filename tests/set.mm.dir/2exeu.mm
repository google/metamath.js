include "wex.mm"
include "weu.mm"
include "wa.mm"
include "wmo.mm"
include "eumo.mm"
include "euex.mm"
include "moimi.mm"
include "syl.mm"
include "2euex.mm"
include "anim12ci.mm"
include "eu5.mm"
include "sylibr.mm"

theorem 2exeu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph )

  proof
    wph
    vy
    wex
    #
    vx
    weu
    #
    wph
    vx
    wex
    vy
    weu
    #
    wa
    wph
    vy
    weu
    #
    vx
    wex
    #
    @3
    vx
    wmo
    #
    wa
    @3
    vx
    weu
    @1
    @5
    @2
    @4
    @1
    @0
    vx
    wmo
    @5
    @0
    vx
    eumo
    @3
    @0
    vx
    wph
    vy
    euex
    moimi
    syl
    wph
    vy
    vx
    2euex
    anim12ci
    @3
    vx
    eu5
    sylibr
end
